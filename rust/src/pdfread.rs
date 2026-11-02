//! pdfread.c: the pages of a PDF, for grimoire/import (docs/EXPORT.md).
//!
//! A PDF is read here only as far as a notebook needs it: each page as one picture. A page that is
//! a whole-page image (a scan, a photographed page, a page KOReader rasterized) is read as that
//! image, at the size it holds. A page set in fonts, or drawn with lines, is drawn here (the second
//! half of this file): its content stream walked, its paths filled and stroked, its text set
//! through the page's own font program (stb_truetype), and its images placed by their matrices. So
//! a born-digital PDF becomes a notebook too, not only a scan.
//!
//! Reading runs in the import's forked child (bgwork_template.rs), never on the UI thread.
//!
//! The objects are found by scanning the file for "N G obj" rather than by its cross-reference table
//! (a table this reader would have to trust, and that many files get slightly wrong): a later
//! definition of an object is the one that counts, as an incremental update means it to be.
//!
//! Everything here runs in the import's forked child. Every read is bounds-checked against the file
//! and every allocation against what a page may take (PDF_MAX_*): a PDF is untrusted input.

use crate::assets::FONT_TERMINESS_REGULAR;
use crate::ffi_stb;
use crate::prelude::*;
use std::collections::HashMap;
use std::ffi::c_char;
use std::rc::Rc;

/// a short line for grimoire.log, as the C's char why[PDF_WHY_LEN]
pub const PDF_WHY_LEN: usize = 96;

/// What reading a PDF (or one of its pages) came to.
pub const PDF_OK: i32 = 0;
/// the file does not read, or is bigger than a PDF Grimoire takes (may pass)
pub const PDF_ERR_READ: i32 = -1;
/// not a PDF, or one this reader cannot follow (it will not pass)
pub const PDF_ERR_FORMAT: i32 = -2;
/// a page has no whole-page picture (text in fonts, vector graphics)
pub const PDF_ERR_NO_PICTURE: i32 = -3;
/// the picture is in a form Grimoire does not decode (JPEG 2000, CCITT...)
pub const PDF_ERR_UNSUPPORTED: i32 = -4;
/// not enough memory (another time there may be)
pub const PDF_ERR_MEM: i32 = -5;

/// the biggest PDF read at all
const PDF_MAX_BYTES: usize = 96 << 20;
/// and the biggest page picture it may hold
const PDF_MAX_PIXELS: i64 = BG_MAX_PIXELS;
/// the most a page's samples (or a decoded JPEG) may take
const PDF_MAX_SAMPLES: usize = 160 << 20;
/// as many pages as a notebook holds
const PDF_MAX_PAGES: usize = 2000;
/// objects in the file
const PDF_MAX_OBJ: usize = 400000;
/// the page tree, and a form's resources, this deep
const PDF_MAX_DEPTH: i32 = 32;

#[derive(Clone, Copy, Default)]
struct Obj {
    num: i32,
    /// just past its "obj": where its value begins
    off: usize,
}

/// The file's bytes, its objects, and the page tree's pages (by object number).
pub struct PdfReader {
    data: Vec<u8>,
    obj: Vec<Obj>,
    pages: Vec<i32>,
}

/// A slice of the file, from p up to e (a default one, 0..0, is the C's NULL).
#[derive(Clone, Copy, Default)]
struct Rng {
    p: usize,
    e: usize,
}

impl Rng {
    fn new(p: usize, e: usize) -> Rng {
        Rng { p, e }
    }
    fn is_null(&self) -> bool {
        self.p == 0 && self.e == 0
    }
}

/// A stream's bytes in the file: where they start, and how many.
#[derive(Clone, Copy, Default)]
struct Stream {
    off: usize,
    len: usize,
}

fn why_set(why: &mut String, text: &str) {
    why.clear();
    let mut end = text.len().min(PDF_WHY_LEN - 1);
    while end > 0 && !text.is_char_boundary(end) {
        end -= 1;
    }
    why.push_str(&text[..end]);
}

// ---- tokens ----

fn is_ws(c: u8) -> bool {
    c == 0 || c == 9 || c == 10 || c == 12 || c == 13 || c == 32
}

fn is_digit(c: u8) -> bool {
    c.is_ascii_digit()
}

fn is_delim(c: u8) -> bool {
    matches!(c, b'(' | b')' | b'<' | b'>' | b'[' | b']' | b'{' | b'}' | b'/' | b'%')
}

fn skip_ws(d: &[u8], mut p: usize, e: usize) -> usize {
    while p < e {
        if is_ws(d[p]) {
            p += 1;
        } else if d[p] == b'%' {
            while p < e && d[p] != b'\n' && d[p] != b'\r' {
                p += 1;
            }
        } else {
            break;
        }
    }
    p
}

// Past a literal string at p (on its '('), its escapes and nested parentheses included.
fn skip_string(d: &[u8], mut p: usize, e: usize) -> usize {
    let mut depth: i32 = 0;
    while p < e {
        if d[p] == b'\\' {
            p += 2;
            continue;
        }
        if d[p] == b'(' {
            depth += 1;
        } else if d[p] == b')' {
            depth -= 1;
            if depth == 0 {
                return p + 1;
            }
        }
        p += 1;
    }
    e
}

// Past one value at p: a dictionary, an array, a string, a name, or a number or keyword.
fn tok_end(d: &[u8], mut p: usize, e: usize) -> usize {
    if p >= e {
        return p;
    }
    if d[p] == b'<' && p + 1 < e && d[p + 1] == b'<' {
        // a dictionary
        let mut depth: i32 = 0;
        while p < e {
            if d[p] == b'<' && p + 1 < e && d[p + 1] == b'<' {
                depth += 1;
                p += 2;
            } else if d[p] == b'>' && p + 1 < e && d[p + 1] == b'>' {
                p += 2;
                depth -= 1;
                if depth == 0 {
                    return p;
                }
            } else if d[p] == b'(' {
                p = skip_string(d, p, e);
            } else if d[p] == b'[' {
                p = array_end(d, p, e);
            } else if d[p] == b'<' {
                // a hex string
                while p < e && d[p] != b'>' {
                    p += 1;
                }
                if p < e {
                    p += 1;
                }
            } else if d[p] == b'%' {
                while p < e && d[p] != b'\n' && d[p] != b'\r' {
                    p += 1;
                }
            } else if d[p] == b'/' {
                p += 1;
                while p < e && !is_ws(d[p]) && !is_delim(d[p]) {
                    p += 1;
                }
            } else {
                p += 1;
            }
        }
        return e;
    }
    if d[p] == b'[' {
        return array_end(d, p, e);
    }
    if d[p] == b'(' {
        return skip_string(d, p, e);
    }
    if d[p] == b'<' {
        p += 1;
        while p < e && d[p] != b'>' {
            p += 1;
        }
        return if p < e { p + 1 } else { e };
    }
    if d[p] == b'/' {
        p += 1;
        while p < e && !is_ws(d[p]) && !is_delim(d[p]) {
            p += 1;
        }
        return p;
    }
    while p < e && !is_ws(d[p]) && !is_delim(d[p]) {
        p += 1;
    }
    p
}

fn array_end(d: &[u8], mut p: usize, e: usize) -> usize {
    let mut depth: i32 = 0;
    while p < e {
        if d[p] == b'[' {
            depth += 1;
            p += 1;
        } else if d[p] == b']' {
            p += 1;
            depth -= 1;
            if depth == 0 {
                return p;
            }
        } else if d[p] == b'(' {
            p = skip_string(d, p, e);
        } else if d[p] == b'<' && p + 1 < e && d[p + 1] == b'<' {
            p = tok_end(d, p, e);
        } else if d[p] == b'<' {
            while p < e && d[p] != b'>' {
                p += 1;
            }
            if p < e {
                p += 1;
            }
        } else if d[p] == b'%' {
            while p < e && d[p] != b'\n' && d[p] != b'\r' {
                p += 1;
            }
        } else {
            p += 1;
        }
    }
    e
}

// Past the value at p, its reference's other two tokens included ("12 0 R").
fn value_end(d: &[u8], p: usize, e: usize) -> usize {
    let a = tok_end(d, p, e);
    let b = skip_ws(d, a, e);
    if b > a && b < e && (is_digit(d[b]) || d[b] == b'-' || d[b] == b'+') {
        // ("12 0 R")
        let c = tok_end(d, b, e);
        let q = skip_ws(d, c, e);
        if q < e && (d[q] == b'R' || d[q] == b'r') && (q + 1 >= e || is_ws(d[q + 1]) || is_delim(d[q + 1])) {
            return q + 1;
        }
    }
    a
}

fn span_is(d: &[u8], v: Rng, s: &str) -> bool {
    !v.is_null() && v.e <= d.len() && v.e - v.p == s.len() && &d[v.p..v.e] == s.as_bytes()
}

// The number in a span, if it is one (as strtol reads its start).
fn span_long(d: &[u8], v: Rng, out: &mut i64) -> bool {
    if v.is_null() || v.e > d.len() || v.e <= v.p {
        return false;
    }
    let mut p = v.p;
    while p < v.e && is_ws(d[p]) {
        p += 1;
    }
    let mut neg = false;
    if p < v.e && (d[p] == b'-' || d[p] == b'+') {
        neg = d[p] == b'-';
        p += 1;
    }
    let start = p;
    let mut n: i64 = 0;
    while p < v.e && is_digit(d[p]) {
        n = n.saturating_mul(10).saturating_add((d[p] - b'0') as i64);
        p += 1;
    }
    if p == start {
        return false;
    }
    *out = if neg { -n } else { n };
    true
}

// Whether the value is an indirect reference ("12 0 R"), and its object number.
fn ref_num(d: &[u8], v: Rng, out: &mut i32) -> bool {
    if v.is_null() || v.e > d.len() || v.e <= v.p {
        return false;
    }
    let mut p = v.p;
    let num_at = |d: &[u8], p: &mut usize, e: usize| -> Option<i64> {
        while *p < e && is_ws(d[*p]) {
            *p += 1;
        }
        let start = *p;
        let mut n: i64 = 0;
        while *p < e && is_digit(d[*p]) {
            n = n.saturating_mul(10).saturating_add((d[*p] - b'0') as i64);
            *p += 1;
        }
        if *p == start {
            None
        } else {
            Some(n)
        }
    };
    let Some(a) = num_at(d, &mut p, v.e) else { return false };
    let Some(_b) = num_at(d, &mut p, v.e) else { return false };
    while p < v.e && is_ws(d[p]) {
        p += 1;
    }
    if p >= v.e || (d[p] != b'R' && d[p] != b'r') || a <= 0 || a > 1000000 {
        return false;
    }
    *out = a as i32;
    true
}

// ---- objects ----

fn find_bytes(d: &[u8], p: usize, e: usize, needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || e > d.len() || e - p < needle.len() {
        return None;
    }
    let mut q = p;
    while q + needle.len() <= e {
        if d[q] == needle[0] && &d[q..q + needle.len()] == needle {
            return Some(q);
        }
        q += 1;
    }
    None
}

fn obj_find(r: &PdfReader, num: i32) -> usize {
    let (mut lo, mut hi) = (0i32, r.obj.len() as i32 - 1);
    while lo <= hi {
        let mid = lo + (hi - lo) / 2;
        let o = r.obj[mid as usize];
        if o.num == num {
            return o.off;
        }
        if o.num < num {
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }
    0
}

fn value_starts(d: &[u8], p: usize, e: usize) -> bool {
    let p = skip_ws(d, p, e);
    if p >= e {
        return false;
    }
    matches!(
        d[p],
        b'<' | b'[' | b'(' | b'/' | b'0'..=b'9' | b'-' | b'+' | b'.' | b't' | b'f' | b'n'
    )
}

// The object at off ("N G obj" scanned): its value, and the bytes of its stream when it has one.
fn obj_parse(r: &PdfReader, off: usize, val: &mut Rng, stream: &mut Option<Stream>, streamed: &mut bool) -> bool {
    let d = &r.data;
    let e = d.len();
    if off == 0 || off >= d.len() {
        return false;
    }
    let p = skip_ws(d, off, e);
    if !value_starts(d, p, e) {
        return false;
    }
    let ve = value_end(d, p, e);
    *val = Rng::new(p, ve);
    *stream = None;
    *streamed = false;
    if d[p] != b'<' || p + 1 >= ve || d[p + 1] != b'<' {
        return true;
    }
    let mut q = skip_ws(d, ve, e);
    if e - q < 6 || &d[q..q + 6] != b"stream" {
        return true;
    }
    *streamed = true;
    q += 6;
    if q < e && d[q] == b'\r' {
        q += 1;
    }
    if q < e && d[q] == b'\n' {
        q += 1;
    }
    // Its /Length, when the file gives one that fits (some writers get it wrong: then its endstream
    // says where it ends).
    let mut len: usize = 0;
    let mut have = false;
    let (kp0, ke) = (val.p + 2, val.e - 2);
    let mut kp = kp0;
    while kp < ke {
        let key_p = skip_ws(d, kp, ke);
        if key_p >= ke || d[key_p] != b'/' {
            break;
        }
        let key_e = tok_end(d, key_p, ke);
        let v = skip_ws(d, key_e, ke);
        if v >= ke {
            break;
        }
        let lv = Rng::new(v, value_end(d, v, ke));
        if span_is(d, Rng::new(key_p, key_e), "/Length") {
            let mut l: i64 = 0;
            if span_long(d, lv, &mut l) {
                have = l > 0;
                len = if have { l as usize } else { 0 };
            } else {
                // an indirect length
                let mut num = 0;
                if ref_num(d, lv, &mut num) {
                    let mut nv = Rng::default();
                    let mut nostream = None;
                    let mut nostreamed = false;
                    if obj_parse(r, obj_find(r, num), &mut nv, &mut nostream, &mut nostreamed)
                        && span_long(d, nv, &mut l)
                        && l > 0
                    {
                        have = true;
                        len = l as usize;
                    }
                }
            }
            break;
        }
        kp = skip_ws(d, lv.e, ke);
    }
    if have && e - q >= len && len <= PDF_MAX_BYTES {
        let after = skip_ws(d, q + len, e);
        if e - after >= 9 && &d[after..after + 9] == b"endstream" {
            *stream = Some(Stream { off: q, len });
            return true;
        }
    }
    let Some(es) = find_bytes(d, q, e, b"endstream") else { return false };
    let mut flen = es - q;
    while flen > 0 && (d[q + flen - 1] == b'\n' || d[q + flen - 1] == b'\r') {
        flen -= 1;
    }
    *stream = Some(Stream { off: q, len: flen });
    true
}

fn obj_value(r: &PdfReader, num: i32, val: &mut Rng) -> bool {
    let mut nostream = None;
    let mut nostreamed = false;
    obj_parse(r, obj_find(r, num), val, &mut nostream, &mut nostreamed)
}

// The value, with any indirect reference followed to what it names.
fn deref(r: &PdfReader, v: &mut Rng) -> bool {
    for _ in 0..8 {
        let mut num = 0;
        if !ref_num(&r.data, *v, &mut num) {
            return true;
        }
        if num == 0 {
            *v = Rng::default();
            return true;
        }
        let mut nv = Rng::default();
        if !obj_value(r, num, &mut nv) {
            return false;
        }
        *v = nv;
    }
    false
}

fn is_dict(d: &[u8], v: Rng) -> bool {
    !v.is_null() && v.e > v.p && v.e <= d.len() && v.e - v.p >= 4 && d[v.p] == b'<' && d[v.p + 1] == b'<'
}

fn is_array(d: &[u8], v: Rng) -> bool {
    !v.is_null() && v.e > v.p && v.e <= d.len() && d[v.p] == b'['
}

// The value of key ("/Type") in dictionary dv, as it is (a reference not followed).
fn dict_get(d: &[u8], dv: Rng, key: &str, val: &mut Rng) -> bool {
    if !is_dict(d, dv) {
        return false;
    }
    let e = dv.e - 2;
    let mut p = skip_ws(d, dv.p + 2, e);
    while p < e {
        let k = tok_end(d, p, e);
        if d[p] == b'/' && span_is(d, Rng::new(p, k), key) {
            let v = skip_ws(d, k, e);
            if v >= e {
                return false;
            }
            *val = Rng::new(v, value_end(d, v, e));
            return true;
        }
        p = skip_ws(d, k, e);
    }
    false
}

// The next name and value of a dictionary (p from dv.p + 2, e dv.e - 2).
fn dict_next(d: &[u8], p: &mut usize, e: usize, key: &mut Rng, val: &mut Rng) -> bool {
    let q = skip_ws(d, *p, e);
    if q >= e || d[q] != b'/' {
        return false;
    }
    key.p = q;
    key.e = tok_end(d, q, e);
    let v = skip_ws(d, key.e, e);
    if v >= e {
        return false;
    }
    val.p = v;
    val.e = value_end(d, v, e);
    *p = skip_ws(d, val.e, e);
    true
}

fn arr_next(d: &[u8], p: &mut usize, e: usize, item: &mut Rng) -> bool {
    let q = skip_ws(d, *p, e);
    if q >= e || d[q] == b']' {
        return false;
    }
    item.p = q;
    item.e = value_end(d, q, e);
    *p = skip_ws(d, item.e, e);
    true
}

// A name's text without its '/', copied ("" when the value is not a name).
fn span_name(d: &[u8], v: Rng, out: &mut String, cap: usize) {
    out.clear();
    if v.is_null() || v.e > d.len() || v.e == 0 || d[v.p] != b'/' {
        return;
    }
    let mut q = v.p + 1;
    while q < v.e && out.len() + 1 < cap {
        out.push(d[q] as char);
        q += 1;
    }
}

// The name key of dictionary dv, followed through references.
fn dict_name(r: &PdfReader, dv: Rng, key: &str, out: &mut String, cap: usize) -> bool {
    let mut v = Rng::default();
    out.clear();
    if !dict_get(&r.data, dv, key, &mut v) || !deref(r, &mut v) {
        return false;
    }
    span_name(&r.data, v, out, cap);
    !out.is_empty()
}

fn dict_long(r: &PdfReader, dv: Rng, key: &str, out: &mut i64) -> bool {
    let mut v = Rng::default();
    if !dict_get(&r.data, dv, key, &mut v) || !deref(r, &mut v) {
        return false;
    }
    span_long(&r.data, v, out)
}

// A dictionary object by its number: for a page or a page tree's node.
fn obj_dict(r: &PdfReader, num: i32, out: &mut Rng) -> bool {
    let mut v = Rng::default();
    if !obj_value(r, num, &mut v) || !deref(r, &mut v) || !is_dict(&r.data, v) {
        return false;
    }
    *out = v;
    true
}

// ---- the file's objects, and its page tree ----

// Every "N G obj" in the file. One whose value does not start the way a value does is a coincidence
// in a stream, not an object; of two with the same number, the later holds it (an update).
fn scan_objects(data: &[u8]) -> Vec<Obj> {
    let mut obj: Vec<Obj> = Vec::new();
    let e = data.len();
    let mut i = 0usize;
    while i + 3 < e {
        if data[i] != b'o' || data[i + 1] != b'b' || data[i + 2] != b'j' {
            i += 1;
            continue;
        }
        if i + 3 < e && !is_ws(data[i + 3]) && !is_delim(data[i + 3]) {
            i += 1;
            continue;
        }
        let mut j = i;
        while j > 0 && is_ws(data[j - 1]) {
            j -= 1;
        }
        let gen_end = j;
        while j > 0 && is_digit(data[j - 1]) {
            j -= 1;
        }
        if j == gen_end {
            i += 1;
            continue;
        }
        if j == 0 || !is_ws(data[j - 1]) {
            i += 1;
            continue;
        }
        while j > 0 && is_ws(data[j - 1]) {
            j -= 1;
        }
        let num_end = j;
        while j > 0 && is_digit(data[j - 1]) {
            j -= 1;
        }
        if j == num_end {
            i += 1;
            continue;
        }
        if j > 0 && !is_ws(data[j - 1]) && !is_delim(data[j - 1]) {
            i += 1;
            continue;
        }
        let num_len = num_end - j;
        if num_len == 0 || num_len > 9 {
            i += 1;
            continue;
        }
        let mut num: i64 = 0;
        for k in j..num_end {
            num = num * 10 + (data[k] - b'0') as i64;
        }
        if num <= 0 || num > 1000000 {
            i += 1;
            continue;
        }
        let off = i + 3;
        if !value_starts(data, off, e) {
            i += 1;
            continue;
        }
        if obj.len() < PDF_MAX_OBJ {
            obj.push(Obj { num: num as i32, off });
        }
        i += 3;
    }
    obj.sort_by(|a, b| if a.num != b.num { a.num.cmp(&b.num) } else { a.off.cmp(&b.off) });
    // One entry a number: the last of its run (its latest definition).
    let mut kept: Vec<Obj> = Vec::with_capacity(obj.len());
    for i in 0..obj.len() {
        if i + 1 < obj.len() && obj[i + 1].num == obj[i].num {
            continue;
        }
        kept.push(obj[i]);
    }
    kept
}

// Reads an unsigned integer from the object stream's header ("2 0 3 40 ...").
fn read_uint(d: &[u8], p: &mut usize) -> Option<usize> {
    while *p < d.len() && is_ws(d[*p]) {
        *p += 1;
    }
    let s = *p;
    let mut v: usize = 0;
    while *p < d.len() && is_digit(d[*p]) {
        v = v.saturating_mul(10).saturating_add((d[*p] - b'0') as usize);
        *p += 1;
    }
    if *p == s { None } else { Some(v) }
}

// PDF 1.5 and later keep most objects in compressed object streams (/Type /ObjStm), which no scan
// for "N G obj" in the file can see: the catalog and the pages of a modern file often live in one.
// Each such stream is decoded and its objects written out, as the text they are, after the file's
// own bytes; scanning again then finds them, and being last they are the definitions that count.
// (A stream is never inside an object stream, so one pass over the file's objects is enough.)
fn expand_object_streams(r: &mut PdfReader) {
    let objs = scan_objects(&r.data);
    let mut extra: Vec<u8> = Vec::new();
    for o in objs {
        let mut dv = Rng::default();
        let mut s = None;
        let mut streamed = false;
        let (n, first, body) = {
            let rr: &PdfReader = r;
            if !obj_parse(rr, o.off, &mut dv, &mut s, &mut streamed) || !is_dict(&rr.data, dv) {
                continue;
            }
            let mut ty = String::new();
            if !dict_name(rr, dv, "/Type", &mut ty, 24) || ty != "ObjStm" {
                continue;
            }
            let Some(s) = s else { continue };
            let mut n: i64 = 0;
            let mut first: i64 = 0;
            if !dict_long(rr, dv, "/N", &mut n) || !dict_long(rr, dv, "/First", &mut first) || n <= 0 || first <= 0 {
                continue;
            }
            let Some(body) = stream_data(rr, dv, s, PDF_MAX_CONTENT) else { continue };
            (n as usize, first as usize, body)
        };
        if n > PDF_MAX_OBJ || first >= body.len() {
            continue;
        }
        let mut p = 0usize;
        let mut pairs: Vec<(i32, usize)> = Vec::new();
        for _ in 0..n {
            let Some(num) = read_uint(&body, &mut p) else { break };
            let Some(off) = read_uint(&body, &mut p) else { break };
            if num > 0 && num <= 1000000 {
                pairs.push((num as i32, off));
            }
        }
        if pairs.is_empty() {
            continue;
        }
        let mut starts: Vec<usize> = pairs.iter().map(|&(_, o)| o).collect();
        starts.sort_unstable();
        for &(num, off) in &pairs {
            let start = first + off;
            if start >= body.len() {
                continue;
            }
            let end = starts.iter().find(|&&x| x > off).map_or(body.len(), |&x| first + x).min(body.len());
            if end <= start {
                continue;
            }
            let mut val = &body[start..end];
            while let Some((&last, rest)) = val.split_last() {
                if is_ws(last) || last == 0 {
                    val = rest;
                } else {
                    break;
                }
            }
            if val.is_empty() {
                continue;
            }
            extra.extend_from_slice(b"\n");
            extra.extend_from_slice(format!("{num} 0 obj\n").as_bytes());
            extra.extend_from_slice(val);
            extra.extend_from_slice(b"\nendobj\n");
        }
    }
    if !extra.is_empty() {
        r.data.extend_from_slice(&extra);
    }
}

// A value a page takes from its parent Pages node when it does not give one itself.
fn inherited(r: &PdfReader, page: Rng, key: &str, out: &mut Rng) -> bool {
    let mut dv = page;
    for _ in 0..8 {
        if dict_get(&r.data, dv, key, out) {
            return true;
        }
        let mut parent = Rng::default();
        if !dict_get(&r.data, dv, "/Parent", &mut parent) || !deref(r, &mut parent) || !is_dict(&r.data, parent) {
            return false;
        }
        dv = parent;
    }
    false
}

fn walk_pages(r: &PdfReader, num: i32, depth: i32, pages: &mut Vec<i32>) {
    if depth > PDF_MAX_DEPTH || pages.len() >= PDF_MAX_PAGES {
        return;
    }
    let mut dv = Rng::default();
    if !obj_dict(r, num, &mut dv) {
        return;
    }
    let mut type_ = String::new();
    dict_name(r, dv, "/Type", &mut type_, 24);
    let mut kids = Rng::default();
    let pages_node = type_ == "Pages" || (type_ != "Page" && dict_get(&r.data, dv, "/Kids", &mut kids));
    if pages_node {
        if !dict_get(&r.data, dv, "/Kids", &mut kids) || !deref(r, &mut kids) || !is_array(&r.data, kids) {
            return;
        }
        let e = kids.e - 1;
        let mut p = kids.p + 1;
        let mut kid = Rng::default();
        while arr_next(&r.data, &mut p, e, &mut kid) {
            let mut k = 0;
            if !ref_num(&r.data, kid, &mut k) {
                continue;
            }
            walk_pages(r, k, depth + 1, pages);
            if pages.len() >= PDF_MAX_PAGES {
                return;
            }
        }
        return;
    }
    pages.push(num);
}

fn find_catalog(r: &PdfReader) -> Option<Rng> {
    for i in 0..r.obj.len() {
        let mut dv = Rng::default();
        if !obj_dict(r, r.obj[i].num, &mut dv) {
            continue;
        }
        let mut type_ = String::new();
        if dict_name(r, dv, "/Type", &mut type_, 24) && type_ == "Catalog" {
            return Some(dv);
        }
    }
    None
}

// Opens path for reading its pages' pictures. 0 with the reader and its page count, or a PDF_ERR_*
// with why set (a short line for grimoire.log).
pub fn pdf_open(path: &str, out: &mut Option<Box<PdfReader>>, npages: &mut i32, why: &mut String) -> i32 {
    *out = None;
    *npages = 0;
    why_set(why, "the file does not read");
    let Some(data) = bgimage_read(path, PDF_MAX_BYTES) else { return PDF_ERR_READ };
    if data.len() < 8 || !data.starts_with(b"%PDF-") {
        why_set(why, "not a PDF");
        return PDF_ERR_FORMAT;
    }
    let mut r = Box::new(PdfReader { data, obj: Vec::new(), pages: Vec::new() });
    expand_object_streams(&mut r);
    r.obj = scan_objects(&r.data);
    let mut pages: Vec<i32> = Vec::new();
    let mut pv = Rng::default();
    if let Some(catalog) = find_catalog(&r) {
        if dict_get(&r.data, catalog, "/Pages", &mut pv) {
            let mut root = 0;
            // (a real PDF names its page tree's root here; an inline one is none)
            if ref_num(&r.data, pv, &mut root) {
                walk_pages(&r, root, 0, &mut pages);
            }
        }
    }
    if pages.is_empty() {
        // no catalog this reader can follow: the file's Pages nodes as they come
        let n = r.obj.len();
        for i in 0..n {
            if !pages.is_empty() {
                break;
            }
            let num = r.obj[i].num;
            let mut dv = Rng::default();
            if !obj_dict(&r, num, &mut dv) {
                continue;
            }
            let mut type_ = String::new();
            if !dict_name(&r, dv, "/Type", &mut type_, 24) || type_ != "Pages" {
                continue;
            }
            let mut parent = Rng::default();
            if dict_get(&r.data, dv, "/Parent", &mut parent) {
                continue; // a child node: its root comes first
            }
            walk_pages(&r, num, 0, &mut pages);
        }
    }
    if pages.is_empty() {
        why_set(why, "no pages this reader can find");
        return PDF_ERR_FORMAT;
    }
    *npages = pages.len() as i32;
    r.pages = pages;
    *out = Some(r);
    PDF_OK
}

/// The pages the reader found.
impl PdfReader {
    pub fn npages(&self) -> i32 {
        self.pages.len() as i32
    }
}

/// The reader's file, its objects and pages, let go (the C's pdf_close).
pub fn pdf_close(r: &mut Option<Box<PdfReader>>) {
    *r = None;
}

// ---- pictures ----

const CS_GRAY: i32 = 1;
const CS_RGB: i32 = 3;
const CS_CMYK: i32 = 4;

#[derive(Clone, Default)]
struct Color {
    /// samples a pixel has (1 for an indexed picture, read through pal)
    comps: i32,
    /// what those samples become: CS_GRAY, CS_RGB or CS_CMYK
    kind: i32,
    pal: Vec<u8>,
    /// the palette's components a step: 1 or 3
    palcomp: i32,
}

fn is_name(d: &[u8], v: Rng, s: &str) -> bool {
    let mut buf = String::new();
    span_name(d, v, &mut buf, 32);
    !buf.is_empty() && buf == s
}

// A literal or hex string's bytes, or None.
fn span_string(d: &[u8], v: Rng) -> Option<Vec<u8>> {
    if v.is_null() || v.e <= v.p || v.e > d.len() {
        return None;
    }
    if d[v.p] == b'(' {
        let mut out: Vec<u8> = Vec::new();
        out.try_reserve_exact(v.e - v.p).ok()?;
        let mut p = v.p + 1;
        let last = v.e - 1;
        while p < last {
            let mut c = d[p];
            if c == b'\\' && p + 1 < last {
                p += 1;
                c = match d[p] {
                    b'n' => b'\n',
                    b'r' => b'\r',
                    b't' => b'\t',
                    b'b' => 8,
                    b'f' => 12,
                    b'\n' => {
                        p += 1;
                        continue;
                    }
                    b'\r' => {
                        if p + 1 < last && d[p + 1] == b'\n' {
                            p += 1;
                        }
                        p += 1;
                        continue;
                    }
                    other => {
                        if (b'0'..=b'7').contains(&other) {
                            let mut val = (other - b'0') as i32;
                            for _ in 0..2 {
                                if p + 1 < last && (b'0'..=b'7').contains(&d[p + 1]) {
                                    p += 1;
                                    val = val * 8 + (d[p] - b'0') as i32;
                                } else {
                                    break;
                                }
                            }
                            val as u8
                        } else {
                            other
                        }
                    }
                };
            }
            out.push(c);
            p += 1;
        }
        return Some(out);
    }
    if d[v.p] == b'<' {
        let mut digits = 0usize;
        let mut p = v.p + 1;
        while p < v.e && d[p] != b'>' {
            if !is_ws(d[p]) {
                digits += 1;
            }
            p += 1;
        }
        let n = digits / 2 + (digits & 1);
        let mut out: Vec<u8> = Vec::new();
        out.try_reserve_exact(n.max(1)).ok()?;
        let mut hi: i32 = -1;
        let mut p = v.p + 1;
        while p < v.e && d[p] != b'>' {
            let dg = match d[p] {
                c @ b'0'..=b'9' => (c - b'0') as i32,
                c @ b'a'..=b'f' => (c - b'a') as i32 + 10,
                c @ b'A'..=b'F' => (c - b'A') as i32 + 10,
                _ => {
                    p += 1;
                    continue;
                }
            };
            if hi < 0 {
                hi = dg;
            } else {
                out.push((hi * 16 + dg) as u8);
                hi = -1;
            }
            p += 1;
        }
        if hi >= 0 {
            out.push((hi * 16) as u8);
        }
        return Some(out);
    }
    None
}

// What a picture's /ColorSpace says: the samples a pixel has, and what they become. false for one
// this reader does not follow (Separation, DeviceN, Pattern).
fn colorspace(r: &PdfReader, cs: Rng, c: &mut Color) -> bool {
    *c = Color::default();
    let mut cs = cs;
    {
        // (the C's loop round this runs once: every path below returns)
        if !deref(r, &mut cs) {
            return false;
        }
        if !is_array(&r.data, cs) {
            if is_name(&r.data, cs, "DeviceGray") || is_name(&r.data, cs, "G") || is_name(&r.data, cs, "CalGray") {
                c.comps = CS_GRAY;
                c.kind = CS_GRAY;
                return true;
            }
            if is_name(&r.data, cs, "DeviceRGB") || is_name(&r.data, cs, "RGB") || is_name(&r.data, cs, "CalRGB") {
                c.comps = CS_RGB;
                c.kind = CS_RGB;
                return true;
            }
            if is_name(&r.data, cs, "DeviceCMYK") || is_name(&r.data, cs, "CMYK") {
                c.comps = 4;
                c.kind = CS_CMYK;
                return true;
            }
            return false;
        }
        let e = cs.e - 1;
        let mut p = cs.p + 1;
        let mut item = [Rng::default(); 5];
        let mut n = 0;
        while n < 5 && arr_next(&r.data, &mut p, e, &mut item[n]) {
            n += 1;
        }
        if n < 1 {
            return false;
        }
        let mut family = String::new();
        span_name(&r.data, item[0], &mut family, 32);
        if family == "ICCBased" && n >= 2 {
            // the profile's stream says how many
            let mut prof = item[1];
            if !deref(r, &mut prof) || !is_dict(&r.data, prof) {
                return false;
            }
            let mut nn: i64 = 0;
            if !dict_long(r, prof, "/N", &mut nn) {
                return false;
            }
            if nn == 1 {
                c.comps = CS_GRAY;
                c.kind = CS_GRAY;
                return true;
            }
            if nn == 3 {
                c.comps = CS_RGB;
                c.kind = CS_RGB;
                return true;
            }
            if nn == 4 {
                c.comps = 4;
                c.kind = CS_CMYK;
                return true;
            }
            return false;
        }
        if family == "CalRGB" {
            c.comps = CS_RGB;
            c.kind = CS_RGB;
            return true;
        }
        if family == "CalGray" {
            c.comps = CS_GRAY;
            c.kind = CS_GRAY;
            return true;
        }
        if (family == "Indexed" || family == "I") && n >= 4 {
            let mut base = Color::default();
            // (no indexed of an indexed)
            if !colorspace(r, item[1], &mut base) || !base.pal.is_empty() {
                return false;
            }
            let mut lk = item[3];
            if !deref(r, &mut lk) {
                return false;
            }
            let Some(pal) = span_string(&r.data, lk) else { return false };
            c.palcomp = if base.kind == CS_GRAY { 1 } else { 3 };
            c.pal = pal;
            c.comps = 1;
            c.kind = base.kind;
            return true;
        }
        false
    }
}

// stb_image's inflate, bounded by cap: the bytes decoded, or None.
fn inflate_to(src: &[u8], cap: usize) -> Option<Vec<u8>> {
    if src.is_empty() || src.len() > i32::MAX as usize || cap == 0 || cap > i32::MAX as usize {
        return None;
    }
    let mut out: Vec<u8> = Vec::new();
    out.try_reserve_exact(cap).ok()?;
    // SAFETY: stbi_zlib_decode_buffer writes at most cap bytes into the buffer out reserved, and
    // reads exactly len bytes from src.
    let n = unsafe {
        ffi_stb::stbi_zlib_decode_buffer(
            out.as_mut_ptr() as *mut c_char,
            cap as i32,
            src.as_ptr() as *const c_char,
            src.len() as i32,
        )
    };
    if n <= 0 {
        return None;
    }
    // SAFETY: the call above wrote n bytes into the buffer, n <= cap, and n > 0; every one of them
    // is initialized, which is what a u8 needs.
    unsafe { out.set_len(n as usize) };
    Some(out)
}

fn paeth(a: i32, b: i32, c: i32) -> i32 {
    let p = a + b - c;
    let (pa, pb, pc) = ((p - a).abs(), (p - b).abs(), (p - c).abs());
    if pa <= pb && pa <= pc {
        return a;
    }
    if pb <= pc {
        return b;
    }
    c
}

// A row of PNG predictors undone (Predictor 10 to 15), in place, into dst (rowbytes a row).
fn unfilter_row(dst: &mut [u8], src: &[u8], rowbytes: usize, kind: i32, prev: Option<&[u8]>, bpp: i32) {
    for i in 0..rowbytes {
        let mut x = src[i] as i32;
        let left = if i >= bpp as usize { dst[i - bpp as usize] as i32 } else { 0 };
        let up = prev.map_or(0, |p| p[i] as i32);
        let upleft = match prev {
            Some(p) if i >= bpp as usize => p[i - bpp as usize] as i32,
            _ => 0,
        };
        match kind {
            1 => x += left,
            2 => x += up,
            3 => x += (left + up) / 2,
            4 => x += paeth(left, up, upleft),
            _ => {}
        }
        dst[i] = x as u8;
    }
}

// Samples as they are (after no filter, Flate, and its predictor undone) into 8-bit components.
fn unpack(d: &[u8], len: usize, w: i32, h: i32, ncomp: i32, bpc: i32, why: &mut String) -> Option<Vec<u8>> {
    let rowbytes = ((w as usize) * (ncomp as usize) * (bpc as usize)).div_ceil(8);
    if rowbytes == 0 || (h as usize) > len / rowbytes {
        // (a file that says less than its rows hold)
        why_set(why, "the page picture is short");
        return None;
    }
    let n = w as usize * h as usize * ncomp as usize;
    let mut out: Vec<u8> = Vec::new();
    if out.try_reserve_exact(n).is_err() {
        why_set(why, "out of memory");
        return None;
    }
    out.resize(n, 0);
    for y in 0..h as usize {
        let row = &d[y * rowbytes..y * rowbytes + rowbytes];
        let o = &mut out[y * w as usize * ncomp as usize..(y + 1) * w as usize * ncomp as usize];
        if bpc == 8 {
            o[..w as usize * ncomp as usize].copy_from_slice(&row[..w as usize * ncomp as usize]);
            continue;
        }
        let mask: i32 = (1 << bpc) - 1;
        let max = mask;
        let mut bit: usize = 0;
        for x in 0..w as usize {
            for c in 0..ncomp as usize {
                let v: i32 = if bpc == 1 {
                    ((row[bit >> 3] >> (7 - (bit & 7))) & 1) as i32
                } else {
                    let byte = bit >> 3;
                    let shift = 8 - bpc as i32 - (bit & 7) as i32;
                    if shift < 0 { 0 } else { ((row[byte] >> shift) & mask as u8) as i32 }
                };
                bit += bpc as usize;
                o[x * ncomp as usize + c] = (v * 255 / max) as u8;
            }
        }
    }
    Some(out)
}

// The page's samples into a picture: gray, RGB, CMYK turned to RGB, or through an indexed palette.
fn samples_picture(samples: &[u8], w: i32, h: i32, c: &Color, out: &mut BgPicture, why: &mut String) -> i32 {
    let ncomp = c.comps as usize;
    let ch = if c.kind == CS_GRAY { 1 } else { 3 };
    let n = w as usize * h as usize;
    let mut px: Vec<u8> = Vec::new();
    if px.try_reserve_exact(n * ch).is_err() {
        why_set(why, "out of memory");
        return PDF_ERR_MEM;
    }
    px.resize(n * ch, 0);
    for i in 0..n {
        let s = &samples[i * ncomp..i * ncomp + ncomp];
        let rgb: [u8; 3];
        if !c.pal.is_empty() {
            let step = c.palcomp.max(1) as usize;
            let at = s[0] as usize * step;
            if at + step > c.pal.len() {
                rgb = [255, 255, 255];
            } else if step == 1 {
                rgb = [c.pal[at], c.pal[at], c.pal[at]];
            } else {
                rgb = [c.pal[at], c.pal[at + 1], c.pal[at + 2]];
            }
        } else if ncomp == 1 {
            rgb = [s[0], s[0], s[0]];
        } else if ncomp == 3 {
            rgb = [s[0], s[1], s[2]];
        } else {
            // CMYK: ink over white paper
            let k = 255 - s[3] as i32;
            rgb = [
                (((255 - s[0] as i32) * k) / 255) as u8,
                (((255 - s[1] as i32) * k) / 255) as u8,
                (((255 - s[2] as i32) * k) / 255) as u8,
            ];
        }
        if ch == 1 {
            px[i] = rgb[0];
        } else {
            px[i * 3] = rgb[0];
            px[i * 3 + 1] = rgb[1];
            px[i * 3 + 2] = rgb[2];
        }
    }
    out.px = px;
    out.w = w;
    out.h = h;
    out.ch = ch as i32;
    PDF_OK
}

fn is_flate(f: &str) -> bool {
    f == "FlateDecode" || f == "Fl"
}

fn is_dct(f: &str) -> bool {
    f == "DCTDecode" || f == "DCT"
}

// How many names /Filter has, into f (at most 3).
fn filters_of(r: &PdfReader, dv: Rng, f: &mut [String; 3]) -> usize {
    let mut n = 0;
    let mut v = Rng::default();
    if !dict_get(&r.data, dv, "/Filter", &mut v) || !deref(r, &mut v) {
        return 0;
    }
    if !is_array(&r.data, v) {
        span_name(&r.data, v, &mut f[0], 24);
        return usize::from(!f[0].is_empty());
    }
    let e = v.e - 1;
    let mut p = v.p + 1;
    let mut item = Rng::default();
    while n < 3 && arr_next(&r.data, &mut p, e, &mut item) {
        let mut x = item;
        if !deref(r, &mut x) {
            continue;
        }
        span_name(&r.data, x, &mut f[n], 24);
        if !f[n].is_empty() {
            n += 1;
        }
    }
    n
}

// Decodes one image XObject (its dictionary and stream) into a picture.
fn decode_image(r: &PdfReader, dv: &Rng, s: &Stream, out: &mut BgPicture, why: &mut String) -> i32 {
    *out = BgPicture::default();
    let (mut w, mut h) = (0i64, 0i64);
    if !dict_long(r, *dv, "/Width", &mut w)
        || !dict_long(r, *dv, "/Height", &mut h)
        || w <= 0
        || h <= 0
        || w > 40000
        || h > 40000
    {
        why_set(why, "the page picture has no size");
        return PDF_ERR_FORMAT;
    }
    if w * h > PDF_MAX_PIXELS {
        why_set(why, "the page picture is too big");
        return PDF_ERR_UNSUPPORTED;
    }
    let mut maskv = Rng::default();
    if dict_get(&r.data, *dv, "/ImageMask", &mut maskv) {
        // (a stencil, not a page: 0 paints, 1 is clear)
        let mut v: i64 = 0;
        if !deref(r, &mut maskv) || !span_long(&r.data, maskv, &mut v) || v != 0 {
            why_set(why, "the page picture is a mask");
            return PDF_ERR_UNSUPPORTED;
        }
    }
    let mut bpc: i64 = 8;
    if !dict_long(r, *dv, "/BitsPerComponent", &mut bpc) {
        bpc = 8;
    }
    if bpc != 1 && bpc != 2 && bpc != 4 && bpc != 8 {
        why_set(why, &cformat!("%ld bits a sample is not read", bpc));
        return PDF_ERR_UNSUPPORTED;
    }
    let mut csv = Rng::default();
    let mut color = Color::default();
    if dict_get(&r.data, *dv, "/ColorSpace", &mut csv) {
        if !colorspace(r, csv, &mut color) {
            why_set(why, "the page picture's colour is not read");
            return PDF_ERR_UNSUPPORTED;
        }
    } else {
        color.comps = CS_GRAY;
        color.kind = CS_GRAY;
    }
    let mut f = [String::new(), String::new(), String::new()];
    let nf = filters_of(r, *dv, &mut f);
    let (mut flate, mut dct) = (-1i32, -1i32);
    for i in 0..nf {
        if is_flate(&f[i]) && flate < 0 {
            flate = i as i32;
        } else if is_dct(&f[i]) && dct < 0 {
            dct = i as i32;
        } else {
            why_set(why, &cformat!("%s is not read", &f[i]));
            return PDF_ERR_UNSUPPORTED;
        }
    }
    let src = &r.data[s.off..s.off + s.len];
    // A JPEG in the file as it is (or after Flate): bgimage_decode reads it, its own checks and all.
    if dct >= 0 {
        let mut jp: &[u8] = src;
        let mut tmp: Option<Vec<u8>> = None;
        if flate >= 0 {
            if dct < flate {
                why_set(why, "the page picture's filters are not read");
                return PDF_ERR_UNSUPPORTED;
            }
            let mut cap = src.len() + (src.len() >> 1) + (1usize << 20);
            if cap > PDF_MAX_SAMPLES {
                cap = PDF_MAX_SAMPLES;
            }
            let Some(inflated) = inflate_to(src, cap) else {
                why_set(why, "the page picture does not read");
                return PDF_ERR_FORMAT;
            };
            tmp = Some(inflated);
            jp = tmp.as_deref().unwrap_or(&[]);
        }
        let mut why2: &'static str = "the picture does not read";
        let rc = bgimage_decode(jp, out, &mut why2);
        drop(tmp);
        if rc != 0 {
            why_set(why, why2);
            return if rc == -2 { PDF_ERR_MEM } else { PDF_ERR_FORMAT };
        }
        return PDF_OK;
    }
    // Raw samples: Flate, or as they are.
    let rowbytes;
    let need;
    let mut pred: i32 = 1;
    let mut pcolors = color.comps;
    let mut pbits = bpc as i32;
    let mut pcols = w as i32;
    {
        let mut parms = Rng::default();
        if dict_get(&r.data, *dv, "/DecodeParms", &mut parms) {
            let mut one = parms;
            if is_array(&r.data, one) {
                let e = one.e - 1;
                let mut p = one.p + 1;
                let mut item = Rng::default();
                if !arr_next(&r.data, &mut p, e, &mut item) {
                    item = Rng::default();
                }
                one = item;
            }
            if deref(r, &mut one) && is_dict(&r.data, one) {
                let mut v: i64 = 1;
                if dict_long(r, one, "/Predictor", &mut v) {
                    pred = v as i32;
                }
                if dict_long(r, one, "/Colors", &mut v) {
                    pcolors = v as i32;
                }
                if dict_long(r, one, "/BitsPerComponent", &mut v) {
                    pbits = v as i32;
                }
                if dict_long(r, one, "/Columns", &mut v) {
                    pcols = v as i32;
                }
            }
        }
        if pcols <= 0 || pcolors <= 0 || (pbits != 1 && pbits != 2 && pbits != 4 && pbits != 8) || pcols > 40000 {
            why_set(why, "the page picture's rows are not read");
            return PDF_ERR_UNSUPPORTED;
        }
        rowbytes = ((pcols as usize) * (pcolors as usize) * (pbits as usize)).div_ceil(8);
        if rowbytes == 0 {
            why_set(why, "the page picture's rows are empty");
            return PDF_ERR_FORMAT;
        }
        let rows = h as usize;
        need = rowbytes * rows + if pred >= 10 { rows } else { 0 };
        if need > PDF_MAX_SAMPLES {
            why_set(why, "the page picture is too big");
            return PDF_ERR_UNSUPPORTED;
        }
    }
    let mut owned: Option<Vec<u8>> = None;
    if flate >= 0 {
        let Some(inflated) = inflate_to(src, need + 4096) else {
            why_set(why, "the page picture does not read");
            return PDF_ERR_FORMAT;
        };
        owned = Some(inflated);
    }
    let (raw, rawlen) = match &owned {
        Some(b) => (b.as_slice(), b.len()),
        None => (src, src.len()),
    };
    // A row's own filter (PNG predictors, or TIFF's differencing) undone.
    let mut rows_buf: Option<Vec<u8>> = None;
    if pred >= 10 {
        let mut bpp = (pcolors * pbits + 7) / 8;
        if bpp < 1 {
            bpp = 1;
        }
        if rawlen < rowbytes * h as usize + h as usize {
            why_set(why, "the page picture is short");
            return PDF_ERR_FORMAT;
        }
        let mut buf: Vec<u8> = Vec::new();
        if buf.try_reserve_exact(rowbytes * h as usize + rowbytes).is_err() {
            why_set(why, "out of memory");
            return PDF_ERR_MEM;
        }
        buf.resize(rowbytes * h as usize, 0);
        for y in 0..h as usize {
            let at = y * (rowbytes + 1);
            let kind = raw[at] as i32;
            let (before, cur) = buf.split_at_mut(y * rowbytes);
            let prev = if y > 0 { Some(&before[(y - 1) * rowbytes..]) } else { None };
            let row = &mut cur[..rowbytes];
            unfilter_row(row, &raw[at + 1..at + 1 + rowbytes], rowbytes, kind, prev, bpp);
        }
        rows_buf = Some(buf);
    } else if pred == 2 {
        // TIFF's horizontal differencing
        let mut buf: Vec<u8> = Vec::new();
        if buf.try_reserve_exact(rowbytes * h as usize).is_err() {
            why_set(why, "out of memory");
            return PDF_ERR_MEM;
        }
        let take = rawlen.min(rowbytes * h as usize);
        buf.extend_from_slice(&raw[..take]);
        buf.resize(rowbytes * h as usize, 0);
        for y in 0..h as usize {
            for i in 1..rowbytes {
                buf[y * rowbytes + i] = buf[y * rowbytes + i].wrapping_add(buf[y * rowbytes + i - 1]);
            }
        }
        rows_buf = Some(buf);
    }
    let samples: &[u8] = match &rows_buf {
        Some(b) => b.as_slice(),
        None => raw,
    };
    let Some(packed) = unpack(samples, rawlen, w as i32, h as i32, color.comps, bpc as i32, why) else {
        return PDF_ERR_FORMAT;
    };
    samples_picture(&packed, w as i32, h as i32, &color, out, why)
}

// The page's biggest picture: an image XObject of its resources, or of a form's resources.
fn scan_xobj(
    r: &PdfReader,
    xo: Rng,
    depth: i32,
    best: &mut i64,
    best_d: &mut Rng,
    best_s: &mut Option<Stream>,
) -> bool {
    if depth > 3 || !is_dict(&r.data, xo) {
        return false;
    }
    let e = xo.e - 2;
    let mut p = xo.p + 2;
    let mut key = Rng::default();
    let mut val = Rng::default();
    while dict_next(&r.data, &mut p, e, &mut key, &mut val) {
        let mut num = 0;
        if !ref_num(&r.data, val, &mut num) {
            continue;
        }
        let mut dv = Rng::default();
        let mut stream = None;
        let mut streamed = false;
        if !obj_parse(r, obj_find(r, num), &mut dv, &mut stream, &mut streamed) || !is_dict(&r.data, dv) {
            continue;
        }
        let mut sub = String::new();
        if !dict_name(r, dv, "/Subtype", &mut sub, 32) {
            continue;
        }
        if sub == "Image" {
            let (mut w, mut h) = (0i64, 0i64);
            if !dict_long(r, dv, "/Width", &mut w) || !dict_long(r, dv, "/Height", &mut h) {
                continue;
            }
            if w <= 0 || h <= 0 || w > 40000 || h > 40000 {
                continue;
            }
            let area = w * h;
            if area > *best && streamed {
                *best = area;
                *best_d = dv;
                *best_s = stream;
            }
        } else if sub == "Form" {
            let mut fres = Rng::default();
            let mut fxo = Rng::default();
            if dict_get(&r.data, dv, "/Resources", &mut fres)
                && deref(r, &mut fres)
                && dict_get(&r.data, fres, "/XObject", &mut fxo)
                && deref(r, &mut fxo)
            {
                scan_xobj(r, fxo, depth + 1, best, best_d, best_s);
            }
        }
    }
    *best > 0
}

fn page_image(r: &PdfReader, page: Rng, img: &mut Rng, s: &mut Option<Stream>) -> bool {
    let mut res = Rng::default();
    let mut xo = Rng::default();
    if !inherited(r, page, "/Resources", &mut res) || !deref(r, &mut res) {
        return false;
    }
    if !dict_get(&r.data, res, "/XObject", &mut xo) || !deref(r, &mut xo) {
        return false;
    }
    let mut best = 0;
    scan_xobj(r, xo, 0, &mut best, img, s)
}

// ---- turning, and down to the size the notebook keeps ----

fn rotate_picture(p: &mut BgPicture, deg: i32) -> i32 {
    let deg = deg.rem_euclid(360);
    if p.px.is_empty() || deg == 0 {
        return 0;
    }
    let (w, h, ch) = (p.w, p.h, p.ch as usize);
    let (nw, nh) = if deg == 180 { (w, h) } else { (h, w) };
    let mut px: Vec<u8> = Vec::new();
    if px.try_reserve_exact(nw as usize * nh as usize * ch).is_err() {
        return -1;
    }
    px.resize(nw as usize * nh as usize * ch, 0);
    for dy in 0..nh {
        for dx in 0..nw {
            let (sx, sy) = if deg == 90 {
                // a quarter turn clockwise
                (dy, h - 1 - dx)
            } else if deg == 180 {
                (w - 1 - dx, h - 1 - dy)
            } else {
                // 270
                (w - 1 - dy, dx)
            };
            let from = (sy as usize * w as usize + sx as usize) * ch;
            let to = (dy as usize * nw as usize + dx as usize) * ch;
            px[to..to + ch].copy_from_slice(&p.px[from..from + ch]);
        }
    }
    p.px = px;
    p.w = nw;
    p.h = nh;
    0
}

// The picture averaged down to at most max_w x max_h (whole blocks, as bgimage_normalize does).
fn shrink_picture(p: &mut BgPicture, max_w: i32, max_h: i32) {
    if p.px.is_empty() || max_w < 1 || max_h < 1 {
        return;
    }
    let mut f: i32 = 1;
    while (p.w + f - 1) / f > max_w || (p.h + f - 1) / f > max_h {
        f += 1;
    }
    if f <= 1 {
        return;
    }
    let mut nw = (p.w + f - 1) / f;
    let mut nh = (p.h + f - 1) / f;
    let ch = p.ch as usize;
    if nw < 1 {
        nw = 1;
    }
    if nh < 1 {
        nh = 1;
    }
    let mut px: Vec<u8> = Vec::new();
    if px.try_reserve_exact(nw as usize * nh as usize * ch).is_err() {
        return;
    }
    px.resize(nw as usize * nh as usize * ch, 0);
    for y in 0..nh as usize {
        for x in 0..nw as usize {
            let mut sum = [0i32; 3];
            let mut n = 0i32;
            let mut by = y as i32 * f;
            while by < (y as i32 + 1) * f && by < p.h {
                let mut bx = x as i32 * f;
                while bx < (x as i32 + 1) * f && bx < p.w {
                    for c in 0..ch {
                        sum[c] += p.px[(by as usize * p.w as usize + bx as usize) * ch + c] as i32;
                    }
                    n += 1;
                    bx += 1;
                }
                by += 1;
            }
            for c in 0..ch {
                px[(y * nw as usize + x) * ch + c] = (if n > 0 { sum[c] / n } else { 255 }) as u8;
            }
        }
    }
    p.px = px;
    p.w = nw;
    p.h = nh;
}

/// Page index (0-based) as a picture of at most max_w x max_h pixels (a bigger one is averaged down),
/// 1 (gray) or 3 (RGB) channels. 0 with out filled, or a PDF_ERR_* with why.
pub fn pdf_page_picture(r: &PdfReader, index: i32, max_w: i32, max_h: i32, out: &mut BgPicture, why: &mut String) -> i32 {
    *out = BgPicture::default();
    if index < 0 || index >= r.pages.len() as i32 {
        why_set(why, "no such page");
        return PDF_ERR_FORMAT;
    }
    let mut page = Rng::default();
    if !obj_dict(r, r.pages[index as usize], &mut page) {
        why_set(why, "the page does not read");
        return PDF_ERR_FORMAT;
    }
    let content = page_content(r, page);
    let mut img = Rng::default();
    let mut s: Option<Stream> = None;
    let pictured = page_image(r, page, &mut img, &mut s) && s.is_some();
    // A page that sets text, or draws lines, has no whole-page picture to take: it is drawn. A page
    // with no picture of its own is drawn too (its pictures may be inside a form, and a blank page
    // is still a page). A page that is only a picture (a scan, a photographed page) is read as the
    // picture it is, at the size it holds.
    let ink = content.as_deref().is_some_and(content_has_ink);
    if ink || !pictured {
        let rc = render_page(r, page, content.as_deref(), max_w, max_h, out, why);
        if rc == PDF_OK {
            return page_fit(r, page, out, max_w, max_h, why);
        }
        *out = BgPicture::default();
        if !pictured || rc == PDF_ERR_MEM || rc == PDF_ERR_READ {
            return rc;
        }
        // (a page this reader cannot draw, that holds a picture: the picture, then)
    }
    let Some(stream) = s else {
        why_set(why, "the page is text or line art, not a page picture");
        return PDF_ERR_NO_PICTURE;
    };
    let rc = decode_image(r, &img, &stream, out, why);
    if rc != PDF_OK {
        return rc;
    }
    page_fit(r, page, out, max_w, max_h, why)
}

// The page as the notebook keeps it: turned by its /Rotate, and averaged down to the page's pixels.
fn page_fit(r: &PdfReader, page: Rng, out: &mut BgPicture, max_w: i32, max_h: i32, why: &mut String) -> i32 {
    let mut rot: i64 = 0;
    let mut rv = Rng::default();
    if inherited(r, page, "/Rotate", &mut rv) && deref(r, &mut rv) {
        span_long(&r.data, rv, &mut rot);
    }
    if rot % 90 == 0 && rotate_picture(out, rot as i32) != 0 {
        *out = BgPicture::default();
        why_set(why, "out of memory");
        return PDF_ERR_MEM;
    }
    shrink_picture(out, max_w, max_h);
    PDF_OK
}

// ---- drawing a page: text, lines and pictures (the page's content stream) ----
//
// A page whose content sets text in a font, or draws with lines, has no whole-page picture to take:
// it is drawn here. This is the few operators a book uses, not all of PDF: filled and stroked paths
// (their fill rules kept), text through the page's own font program (stb_truetype; Grimoire's own
// face where the program is CFF, Type 1 or missing, so the text still reads and sits where it
// should), images placed by their matrices, and forms, recursively. Not drawn: transparency groups
// (a fill's alpha is kept, a group's blending is not), shadings, patterns, and inline images.

/// the biggest content stream (a page's, or a form's) drawn
const PDF_MAX_CONTENT: usize = 48 << 20;
/// the biggest font program taken from a file
const PDF_MAX_FONT: usize = 32 << 20;
/// the biggest /ToUnicode table read
const PDF_MAX_CMAP: usize = 4 << 20;

/// A PDF matrix [a b c d e f], column vectors: a point (x, y) maps to
/// (a x + c y + e, b x + d y + f).
type Mat6 = [f32; 6];

fn mat_id() -> Mat6 {
    [1.0, 0.0, 0.0, 1.0, 0.0, 0.0]
}

// m1 x m2: m2 first, then m1.
fn mat_mul(m1: &Mat6, m2: &Mat6) -> Mat6 {
    [
        m1[0] * m2[0] + m1[2] * m2[1],
        m1[1] * m2[0] + m1[3] * m2[1],
        m1[0] * m2[2] + m1[2] * m2[3],
        m1[1] * m2[2] + m1[3] * m2[3],
        m1[0] * m2[4] + m1[2] * m2[5] + m1[4],
        m1[1] * m2[4] + m1[3] * m2[5] + m1[5],
    ]
}

fn mat_pt(m: &Mat6, x: f32, y: f32) -> (f32, f32) {
    (m[0] * x + m[2] * y + m[4], m[1] * x + m[3] * y + m[5])
}

fn mat_inv(m: &Mat6) -> Option<Mat6> {
    let det = m[0] * m[3] - m[1] * m[2];
    if !det.is_finite() || det.abs() < 1.0e-9 {
        return None;
    }
    let k = 1.0 / det;
    Some([
        m[3] * k,
        -m[1] * k,
        -m[2] * k,
        m[0] * k,
        (m[2] * m[5] - m[3] * m[4]) * k,
        (m[1] * m[4] - m[0] * m[5]) * k,
    ])
}

// How much a matrix grows a pixel: the mean of its two rows' lengths.
fn mat_scale(m: &Mat6) -> f32 {
    let a = (m[0] * m[0] + m[1] * m[1]).sqrt();
    let b = (m[2] * m[2] + m[3] * m[3]).sqrt();
    let s = (a + b) * 0.5;
    if s.is_finite() { s } else { 1.0 }
}

/// The page's canvas: RGB, white paper, rows top first.
struct Canvas3 {
    w: usize,
    h: usize,
    px: Vec<u8>,
}

impl Canvas3 {
    fn white(w: usize, h: usize) -> Option<Canvas3> {
        if w == 0 || h == 0 {
            return None;
        }
        let n = w.checked_mul(h)?.checked_mul(3)?;
        if n > PDF_MAX_SAMPLES {
            return None;
        }
        let mut px: Vec<u8> = Vec::new();
        px.try_reserve_exact(n).ok()?;
        px.resize(n, 255);
        Some(Canvas3 { w, h, px })
    }

    fn blend(&mut self, x: usize, y: usize, col: [u8; 3], a: f32) {
        if x >= self.w || y >= self.h || !(a > 0.0) {
            return;
        }
        let a = if a > 1.0 { 1.0 } else { a };
        let i = (y * self.w + x) * 3;
        for c in 0..3 {
            let d = self.px[i + c] as f32;
            self.px[i + c] = (d + (col[c] as f32 - d) * a + 0.5) as u8;
        }
    }
}

/// A rectangle of pixels, x0/y0 up to but not including x1/y1.
#[derive(Clone, Copy, Default)]
struct RectI {
    x0: i32,
    y0: i32,
    x1: i32,
    y1: i32,
}

impl RectI {
    fn whole(w: i32, h: i32) -> RectI {
        RectI { x0: 0, y0: 0, x1: w, y1: h }
    }
    fn clip_to(&self, o: RectI) -> RectI {
        RectI {
            x0: self.x0.max(o.x0),
            y0: self.y0.max(o.y0),
            x1: self.x1.min(o.x1),
            y1: self.y1.min(o.y1),
        }
    }
    fn is_empty(&self) -> bool {
        self.x0 >= self.x1 || self.y0 >= self.y1
    }
}

/// The path being built, in device pixels (already through the page's matrix and the CTM).
#[derive(Default)]
struct PgPath {
    sub: Vec<Vec<(f32, f32)>>,
    cur: Vec<(f32, f32)>,
    start: Option<(f32, f32)>,
    last: Option<(f32, f32)>,
    bb: [f32; 4],
    any: bool,
}

impl PgPath {
    fn reset(&mut self) {
        *self = PgPath::default();
    }
    fn note(&mut self, x: f32, y: f32) {
        if !x.is_finite() || !y.is_finite() || x.abs() > 1.0e6 || y.abs() > 1.0e6 {
            return;
        }
        if !self.any {
            self.bb = [x, y, x, y];
            self.any = true;
            return;
        }
        self.bb[0] = self.bb[0].min(x);
        self.bb[1] = self.bb[1].min(y);
        self.bb[2] = self.bb[2].max(x);
        self.bb[3] = self.bb[3].max(y);
    }
    fn move_to(&mut self, x: f32, y: f32) {
        self.flush();
        self.note(x, y);
        self.cur.push((x, y));
        self.start = Some((x, y));
        self.last = Some((x, y));
    }
    fn line_to(&mut self, x: f32, y: f32) {
        if !x.is_finite() || !y.is_finite() {
            return;
        }
        if self.cur.is_empty() {
            let s = self.start.or(self.last).unwrap_or((x, y));
            self.cur.push(s);
        }
        self.note(x, y);
        self.cur.push((x, y));
        self.last = Some((x, y));
    }
    fn cubic_to(&mut self, c1: (f32, f32), c2: (f32, f32), p: (f32, f32)) {
        if !p.0.is_finite() || !p.1.is_finite() || !c1.0.is_finite() || !c1.1.is_finite() || !c2.0.is_finite() || !c2.1.is_finite() {
            return;
        }
        let Some(p0) = self.last else {
            self.move_to(p.0, p.1);
            return;
        };
        if self.cur.is_empty() {
            self.cur.push(p0);
        }
        flatten_cubic(&mut self.cur, p0, c1, c2, p, 0);
        self.note(p.0, p.1);
        self.note(c1.0, c1.1);
        self.note(c2.0, c2.1);
        self.last = Some(p);
    }
    fn quad_to(&mut self, q: (f32, f32), p: (f32, f32)) {
        let Some(p0) = self.last else {
            self.move_to(p.0, p.1);
            return;
        };
        let c1 = (p0.0 + (q.0 - p0.0) * (2.0 / 3.0), p0.1 + (q.1 - p0.1) * (2.0 / 3.0));
        let c2 = (p.0 + (q.0 - p.0) * (2.0 / 3.0), p.1 + (q.1 - p.1) * (2.0 / 3.0));
        self.cubic_to(c1, c2, p);
    }
    fn close(&mut self) {
        if let Some(s) = self.start {
            if let Some(l) = self.last {
                if (l.0 - s.0).abs() > 0.01 || (l.1 - s.1).abs() > 0.01 {
                    self.line_to(s.0, s.1);
                }
            }
            self.flush();
            self.cur.push(s);
            self.last = Some(s);
        }
    }
    fn flush(&mut self) {
        if self.cur.len() >= 2 {
            self.sub.push(std::mem::take(&mut self.cur));
        } else {
            self.cur.clear();
        }
    }
    fn done(&mut self) {
        self.flush();
    }
    fn bbox_rect(&self, clip: RectI) -> RectI {
        if !self.any {
            return RectI::default();
        }
        RectI {
            x0: (self.bb[0].floor() as i32).saturating_sub(1),
            y0: (self.bb[1].floor() as i32).saturating_sub(1),
            x1: (self.bb[2].ceil() as i32).saturating_add(1),
            y1: (self.bb[3].ceil() as i32).saturating_add(1),
        }
        .clip_to(clip)
    }
}

fn flat_enough(p0: (f32, f32), p1: (f32, f32), p2: (f32, f32), p3: (f32, f32)) -> bool {
    let dx = p3.0 - p0.0;
    let dy = p3.1 - p0.1;
    let len = (dx * dx + dy * dy).sqrt().max(1.0);
    let d1 = ((p1.0 - p0.0) * dy - (p1.1 - p0.1) * dx).abs() / len;
    let d2 = ((p2.0 - p0.0) * dy - (p2.1 - p0.1) * dx).abs() / len;
    d1 < 0.2 && d2 < 0.2
}

fn flatten_cubic(out: &mut Vec<(f32, f32)>, p0: (f32, f32), p1: (f32, f32), p2: (f32, f32), p3: (f32, f32), depth: i32) {
    if depth >= 6 || flat_enough(p0, p1, p2, p3) {
        out.push(p3);
        return;
    }
    let mid = |a: (f32, f32), b: (f32, f32)| ((a.0 + b.0) * 0.5, (a.1 + b.1) * 0.5);
    let a = mid(p0, p1);
    let b = mid(p1, p2);
    let c = mid(p2, p3);
    let d = mid(a, b);
    let e = mid(b, c);
    let f = mid(d, e);
    flatten_cubic(out, p0, a, d, f, depth + 1);
    flatten_cubic(out, f, e, c, p3, depth + 1);
}

#[derive(Clone, Copy)]
struct PgEdge {
    y0: f32,
    y1: f32,
    x0: f32,
    dx: f32,
    dir: i32,
}

// A span [a, b) of a scanline into a row's coverage, x0 being the row's first pixel.
fn add_span(row: &mut [f32], a: f32, b: f32, x0: i32) {
    let mut a = a - x0 as f32;
    let mut b = b - x0 as f32;
    if b < a {
        std::mem::swap(&mut a, &mut b);
    }
    let n = row.len() as f32;
    if !(b > 0.0) || !(a < n) || !a.is_finite() || !b.is_finite() {
        return;
    }
    let a = a.max(0.0);
    let b = b.min(n);
    let i0 = a.floor() as usize;
    let i1 = ((b.ceil() as usize).max(1) - 1).min(row.len() - 1);
    if i0 >= row.len() {
        return;
    }
    if i0 == i1 {
        row[i0] += b - a;
        return;
    }
    row[i0] += (i0 as f32 + 1.0 - a).min(1.0);
    for i in i0 + 1..i1 {
        row[i] += 1.0;
    }
    row[i1] += (b - i1 as f32).min(1.0);
}

// Fills the closed polylines (device pixels) with the nonzero winding rule, or the even-odd one,
// four sub-scanlines a row and exact coverage across it.
fn fill_polys(c: &mut Canvas3, polys: &[Vec<(f32, f32)>], colour: [u8; 3], alpha: f32, even_odd: bool, clip: RectI) {
    if !(alpha > 0.0) || clip.is_empty() {
        return;
    }
    let mut edges: Vec<PgEdge> = Vec::new();
    let (mut bx0, mut by0, mut bx1, mut by1) = (f32::MAX, f32::MAX, f32::MIN, f32::MIN);
    for poly in polys {
        if poly.len() < 2 {
            continue;
        }
        for i in 0..poly.len() {
            let (x0, y0) = poly[i];
            let (x1, y1) = poly[(i + 1) % poly.len()];
            if !x0.is_finite() || !y0.is_finite() || !x1.is_finite() || !y1.is_finite() {
                continue;
            }
            bx0 = bx0.min(x0).min(x1);
            by0 = by0.min(y0).min(y1);
            bx1 = bx1.max(x0).max(x1);
            by1 = by1.max(y0).max(y1);
            if y0 == y1 {
                continue;
            }
            let (ya, yb, xa, xb, dir) = if y0 < y1 { (y0, y1, x0, x1, 1) } else { (y1, y0, x1, x0, -1) };
            edges.push(PgEdge { y0: ya, y1: yb, x0: xa, dx: (xb - xa) / (yb - ya), dir });
        }
    }
    if edges.is_empty() {
        return;
    }
    edges.sort_by(|a, b| a.y0.partial_cmp(&b.y0).unwrap_or(std::cmp::Ordering::Equal));
    // Only the pixels the path covers are scanned (a glyph is its box, not the page).
    let cx0 = clip.x0.max(bx0.floor() as i32).max(0);
    let cx1 = clip.x1.min((bx1.ceil() as i32).saturating_add(1)).min(c.w as i32);
    let y0 = clip.y0.max(by0.floor() as i32).max(0);
    let y1 = clip.y1.min((by1.ceil() as i32).saturating_add(1)).min(c.h as i32);
    if cx1 <= cx0 || y1 <= y0 {
        return;
    }
    let cw = (cx1 - cx0) as usize;
    let mut row: Vec<f32> = vec![0.0; cw];
    let mut active: Vec<usize> = Vec::new();
    let mut next = 0usize;
    let mut xs: Vec<(f32, i32)> = Vec::new();
    const SS: i32 = 4;
    for y in y0..y1 {
        for v in row.iter_mut() {
            *v = 0.0;
        }
        for s in 0..SS {
            let sy = y as f32 + (s as f32 + 0.5) / SS as f32;
            while next < edges.len() && edges[next].y0 <= sy {
                active.push(next);
                next += 1;
            }
            active.retain(|&i| edges[i].y1 > sy);
            xs.clear();
            for &i in &active {
                let e = &edges[i];
                if e.y0 > sy || e.y1 <= sy {
                    continue;
                }
                xs.push((e.x0 + (sy - e.y0) * e.dx, e.dir));
            }
            if xs.len() < 2 {
                continue;
            }
            xs.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
            let mut wind = 0i32;
            let mut open: Option<f32> = None;
            for &(x, dir) in xs.iter() {
                let was = if even_odd { wind & 1 != 0 } else { wind != 0 };
                wind += if even_odd { 1 } else { dir };
                let now = if even_odd { wind & 1 != 0 } else { wind != 0 };
                if !was && now {
                    open = Some(x);
                } else if was && !now {
                    if let Some(a) = open.take() {
                        add_span(&mut row, a, x, cx0);
                    }
                }
            }
        }
        let k = alpha / SS as f32;
        for i in 0..cw {
            if row[i] > 0.0 {
                c.blend((cx0 + i as i32) as usize, y as usize, colour, row[i] * k);
            }
        }
    }
}

// Strokes the polylines: a quad a segment, a small square a join. Dashes are drawn solid.
fn stroke_polys(c: &mut Canvas3, polys: &[Vec<(f32, f32)>], width: f32, colour: [u8; 3], alpha: f32, clip: RectI) {
    let hw = width.max(0.4) * 0.5;
    let mut quads: Vec<Vec<(f32, f32)>> = Vec::new();
    for poly in polys {
        if poly.len() < 2 {
            continue;
        }
        for i in 0..poly.len() - 1 {
            let (x0, y0) = poly[i];
            let (x1, y1) = poly[i + 1];
            let dx = x1 - x0;
            let dy = y1 - y0;
            let len = (dx * dx + dy * dy).sqrt();
            if !(len > 0.01) {
                continue;
            }
            let (nx, ny) = (-dy / len * hw, dx / len * hw);
            quads.push(vec![(x0 + nx, y0 + ny), (x1 + nx, y1 + ny), (x1 - nx, y1 - ny), (x0 - nx, y0 - ny)]);
        }
        for i in 1..poly.len() - 1 {
            let (x, y) = poly[i];
            quads.push(vec![(x - hw, y - hw), (x + hw, y - hw), (x + hw, y + hw), (x - hw, y + hw)]);
        }
    }
    if quads.is_empty() {
        return;
    }
    fill_polys(c, &quads, colour, alpha, false, clip);
}

// A glyph's outline through `m` (font units to device pixels), as the path's contours.
fn glyph_polys(path: &mut PgPath, info: &ffi_stb::stbtt_fontinfo, gid: i32, em: f32, m: &Mat6) -> bool {
    if gid < 0 {
        return false;
    }
    let mut verts: *mut ffi_stb::stbtt_vertex = std::ptr::null_mut();
    // SAFETY: info is an initialized face whose data outlives this call; the shape is a block stb
    // allocates, which stbtt_FreeShape frees below.
    let n = unsafe { ffi_stb::stbtt_GetGlyphShape(info, gid, &mut verts) };
    if n <= 0 || verts.is_null() {
        return false;
    }
    // SAFETY: the call returned n vertices in a block of its own, valid until the free below.
    let vs = unsafe { std::slice::from_raw_parts(verts, n as usize) };
    let tp = |x: i16, y: i16| mat_pt(m, x as f32 * em, y as f32 * em);
    let mut started = false;
    for v in vs {
        match v.type_ {
            1 => {
                let p = tp(v.x, v.y);
                path.move_to(p.0, p.1);
                started = true;
            }
            2 => {
                if started {
                    let p = tp(v.x, v.y);
                    path.line_to(p.0, p.1);
                }
            }
            3 => {
                if started {
                    let q = tp(v.cx, v.cy);
                    let p = tp(v.x, v.y);
                    path.quad_to(q, p);
                }
            }
            4 => {
                if started {
                    let a = tp(v.cx, v.cy);
                    let b = tp(v.cx1, v.cy1);
                    let p = tp(v.x, v.y);
                    path.cubic_to(a, b, p);
                }
            }
            _ => {}
        }
    }
    // SAFETY: the block is stb's, from the call above, freed once.
    unsafe { ffi_stb::stbtt_FreeShape(info, verts) };
    path.done();
    true
}

/// A content stream's operand.
enum Opnd {
    Num(f32),
    Name(String),
    Str(Vec<u8>),
    Arr(Vec<Opnd>),
    /// an inline dictionary (a marked content's properties): read past, not used
    Dict,
}

fn on(ops: &[Opnd], i: usize) -> f32 {
    match ops.get(i) {
        Some(Opnd::Num(v)) => *v,
        _ => 0.0,
    }
}

fn oname(ops: &[Opnd], i: usize) -> String {
    match ops.get(i) {
        Some(Opnd::Name(s)) => s.clone(),
        _ => String::new(),
    }
}

fn ostr(ops: &[Opnd], i: usize) -> Vec<u8> {
    match ops.get(i) {
        Some(Opnd::Str(s)) => s.clone(),
        _ => Vec::new(),
    }
}

fn clamp01(v: f32) -> f32 {
    if v.is_finite() { v.clamp(0.0, 1.0) } else { 0.0 }
}

fn gray8(v: f32) -> [u8; 3] {
    let g = (clamp01(v) * 255.0 + 0.5) as u8;
    [g, g, g]
}

fn rgb8(r: f32, g: f32, b: f32) -> [u8; 3] {
    [(clamp01(r) * 255.0 + 0.5) as u8, (clamp01(g) * 255.0 + 0.5) as u8, (clamp01(b) * 255.0 + 0.5) as u8]
}

fn cmyk8(c: f32, m: f32, y: f32, k: f32) -> [u8; 3] {
    let k = clamp01(k);
    let f = |a: f32| (((1.0 - clamp01(a)) * (1.0 - k)) * 255.0 + 0.5) as u8;
    [f(c), f(m), f(y)]
}

// A number's text, as a content stream writes it.
fn num_of_token(tok: &[u8]) -> Option<f32> {
    if tok.is_empty() || tok.len() > 24 {
        return None;
    }
    let s = std::str::from_utf8(tok).ok()?;
    let v = s.parse::<f32>().ok()?;
    if v.is_finite() { Some(v) } else { None }
}

fn span_f32(d: &[u8], v: Rng) -> Option<f32> {
    if v.is_null() || v.e > d.len() || v.e <= v.p {
        return None;
    }
    let s = std::str::from_utf8(&d[v.p..v.e]).ok()?;
    let x = s.trim().parse::<f32>().ok()?;
    if x.is_finite() { Some(x) } else { None }
}

fn dict_f32(r: &PdfReader, dv: Rng, key: &str) -> Option<f32> {
    let mut v = Rng::default();
    if !dict_get(&r.data, dv, key, &mut v) || !deref(r, &mut v) {
        return None;
    }
    span_f32(&r.data, v)
}

fn array_nums(d: &[u8], v: Rng, out: &mut [f32; 8]) -> usize {
    if !is_array(d, v) {
        return 0;
    }
    let e = v.e - 1;
    let mut p = v.p + 1;
    let mut it = Rng::default();
    let mut n = 0;
    while n < out.len() && arr_next(d, &mut p, e, &mut it) {
        match span_f32(d, it) {
            Some(x) => {
                out[n] = x;
                n += 1;
            }
            None => break,
        }
    }
    n
}

// A content stream's next operand at p (a name, a string, an array, a dictionary, a number), with p
// left where the caller found it when the next token is an operator.
fn content_operand(d: &[u8], p: &mut usize, e: usize, depth: i32) -> Option<Opnd> {
    if depth > 12 {
        return None;
    }
    let start = *p;
    let q = skip_ws(d, *p, e);
    if q >= e {
        return None;
    }
    match d[q] {
        b'/' => {
            let ke = tok_end(d, q, e);
            let mut s = String::new();
            span_name(d, Rng::new(q, ke), &mut s, 64);
            *p = ke;
            Some(Opnd::Name(s))
        }
        b'(' => {
            let ke = skip_string(d, q, e);
            let s = span_string(d, Rng::new(q, ke))?;
            *p = ke;
            Some(Opnd::Str(s))
        }
        b'<' if q + 1 < e && d[q + 1] == b'<' => {
            let ke = tok_end(d, q, e);
            *p = ke;
            Some(Opnd::Dict)
        }
        b'<' => {
            let ke = tok_end(d, q, e);
            let s = span_string(d, Rng::new(q, ke))?;
            *p = ke;
            Some(Opnd::Str(s))
        }
        b'[' => {
            let end = array_end(d, q, e);
            let ie = end.saturating_sub(1);
            let mut items: Vec<Opnd> = Vec::new();
            let mut i = q + 1;
            while i < ie {
                match content_operand(d, &mut i, ie, depth + 1) {
                    Some(v) => {
                        if items.len() < 4096 {
                            items.push(v);
                        }
                    }
                    None => {
                        let t = skip_ws(d, i, ie);
                        if t >= ie {
                            break;
                        }
                        let ke = tok_end(d, t, ie);
                        i = if ke > t { ke } else { t + 1 };
                    }
                }
            }
            *p = end;
            Some(Opnd::Arr(items))
        }
        _ => {
            let ke = tok_end(d, q, e);
            if ke <= q {
                *p = start;
                return None;
            }
            if let Some(v) = num_of_token(&d[q..ke]) {
                *p = ke;
                return Some(Opnd::Num(v));
            }
            *p = start;
            None
        }
    }
}

/// A page's font, as far as drawing it goes: what its codes advance by (the PDF's widths, not the
/// program's: a subset font's are often zeroed), which characters they are, and the font program
/// when it is TrueType (stb_truetype reads it; a CFF or Type 1 program is not read, and the text is
/// drawn with Grimoire's own face instead).
struct PdfFont {
    /// the program, kept alive for the face below (which points into it)
    data: Option<Vec<u8>>,
    info: Option<Box<ffi_stb::stbtt_fontinfo>>,
    /// 1/unitsPerEm
    em: f32,
    /// a composite font (Type0): two-byte codes, and its CIDs are its glyph ids
    composite: bool,
    first: i32,
    widths: Vec<f32>,
    missing: f32,
    /// a composite font's /W: ranges of CIDs and their widths
    cws: Vec<(i32, i32, f32)>,
    dw: f32,
    /// code to character, from /Encoding's names and then /ToUnicode
    uni: Vec<(u32, u32)>,
    cid2gid: Option<Vec<u8>>,
}

impl PdfFont {
    fn plain() -> PdfFont {
        PdfFont {
            data: None,
            info: None,
            em: 0.001,
            composite: false,
            first: 0,
            widths: Vec::new(),
            missing: 500.0,
            cws: Vec::new(),
            dw: 1000.0,
            uni: Vec::new(),
            cid2gid: None,
        }
    }

    fn width(&self, code: u32) -> f32 {
        if self.composite {
            let c = code as i32;
            for &(lo, hi, w) in &self.cws {
                if c >= lo && c <= hi {
                    return w;
                }
            }
            self.dw
        } else {
            let i = code as i32 - self.first;
            if i >= 0 && (i as usize) < self.widths.len() {
                self.widths[i as usize]
            } else {
                self.missing
            }
        }
    }

    fn unicode_of(&self, code: u32) -> u32 {
        for &(c, u) in self.uni.iter().rev() {
            if c == code {
                return u;
            }
        }
        code
    }

    fn gid(&self, code: u32) -> Option<i32> {
        let info = self.info.as_deref()?;
        if self.composite {
            if let Some(map) = &self.cid2gid {
                let at = code as usize * 2;
                if at + 1 >= map.len() {
                    return None;
                }
                let gid = ((map[at] as i32) << 8) | map[at + 1] as i32;
                return if gid > 0 { Some(gid) } else { None };
            }
            return Some(code as i32);
        }
        let u = char_of(self.unicode_of(code));
        // SAFETY: info is a face initialized from a program this font keeps alive.
        let mut gid = unsafe { ffi_stb::stbtt_FindGlyphIndex(info, u as i32) };
        if gid == 0 {
            gid = unsafe { ffi_stb::stbtt_FindGlyphIndex(info, code as i32) };
        }
        if gid > 0 { Some(gid) } else { None }
    }
}

// A resource's font dictionary, as a PdfFont.
fn load_font(r: &PdfReader, fd: Rng) -> PdfFont {
    let mut f = PdfFont::plain();
    let mut sub = String::new();
    dict_name(r, fd, "/Subtype", &mut sub, 24);
    f.composite = sub == "Type0";
    // The dictionary carrying the widths and the program: a simple font's own, or a composite
    // font's CIDFont descendant.
    let mut desc = fd;
    if f.composite {
        let mut d = Rng::default();
        if dict_get(&r.data, fd, "/DescendantFonts", &mut d) && deref(r, &mut d) && is_array(&r.data, d) {
            let e = d.e - 1;
            let mut p = d.p + 1;
            let mut it = Rng::default();
            while arr_next(&r.data, &mut p, e, &mut it) {
                let mut v = it;
                if deref(r, &mut v) && is_dict(&r.data, v) {
                    desc = v;
                    break;
                }
            }
        }
    }
    if f.composite {
        if let Some(x) = dict_f32(r, desc, "/DW") {
            f.dw = x;
        }
        let mut w = Rng::default();
        if dict_get(&r.data, desc, "/W", &mut w) && deref(r, &mut w) && is_array(&r.data, w) {
            cid_widths(r, w, &mut f.cws);
        }
    } else {
        let mut fc = 0i64;
        if dict_long(r, fd, "/FirstChar", &mut fc) {
            f.first = fc as i32;
        }
        let mut w = Rng::default();
        if dict_get(&r.data, fd, "/Widths", &mut w) && deref(r, &mut w) && is_array(&r.data, w) {
            let e = w.e - 1;
            let mut p = w.p + 1;
            let mut it = Rng::default();
            while arr_next(&r.data, &mut p, e, &mut it) {
                f.widths.push(span_f32(&r.data, it).unwrap_or(0.0));
            }
        }
    }
    // The descriptor: its missing width, and the font program.
    let mut fdv = Rng::default();
    let mut have_desc = dict_get(&r.data, desc, "/FontDescriptor", &mut fdv) && deref(r, &mut fdv) && is_dict(&r.data, fdv);
    if !have_desc && (desc.p != fd.p || desc.e != fd.e) {
        have_desc = dict_get(&r.data, fd, "/FontDescriptor", &mut fdv) && deref(r, &mut fdv) && is_dict(&r.data, fdv);
    }
    if have_desc {
        if let Some(x) = dict_f32(r, fdv, "/MissingWidth") {
            if x > 0.0 {
                f.missing = x;
            }
        }
        for key in ["/FontFile2", "/FontFile3", "/FontFile"] {
            let mut v = Rng::default();
            if !dict_get(&r.data, fdv, key, &mut v) {
                continue;
            }
            let mut num = 0;
            if !ref_num(&r.data, v, &mut num) {
                continue;
            }
            let mut dv = Rng::default();
            let mut s = None;
            let mut streamed = false;
            if !obj_parse(r, obj_find(r, num), &mut dv, &mut s, &mut streamed) {
                continue;
            }
            let Some(s) = s else { continue };
            if key == "/FontFile3" {
                // (an OpenType with TrueType outlines reads; CFF and Type 1 do not)
                let mut ss = String::new();
                if dict_name(r, dv, "/Subtype", &mut ss, 16) && ss != "OpenType" {
                    continue;
                }
            }
            let Some(data) = stream_data(r, dv, s, PDF_MAX_FONT) else { continue };
            if data.len() < 12 {
                continue;
            }
            let mut prog = data;
            let mut info = Box::new(ffi_stb::stbtt_fontinfo::default());
            // SAFETY: prog is a font program of prog.len() bytes; stb reads at most that many.
            let off = unsafe { ffi_stb::stbtt_GetFontOffsetForIndex(prog.as_ptr(), 0) };
            let mut good = off >= 0 && unsafe { ffi_stb::stbtt_InitFont(&mut *info, prog.as_ptr(), off) } != 0;
            if !good {
                // (a subset with no cmap: stb_truetype refuses it, so one is built for it)
                if let Some(patched) = with_cmap(&prog) {
                    prog = patched;
                    // SAFETY: prog is the same program in a copy of itself, cmap table added.
                    good = unsafe { ffi_stb::stbtt_InitFont(&mut *info, prog.as_ptr(), 0) } != 0;
                }
            }
            if good {
                // SAFETY: info was just initialized from prog.
                let em = unsafe { ffi_stb::stbtt_ScaleForMappingEmToPixels(&*info, 1.0) };
                f.em = if em > 0.0 && em.is_finite() { em } else { 0.001 };
                f.info = Some(info);
                f.data = Some(prog); // (the face points into it: it outlives the face)
            }
            break;
        }
    }
    // Codes to characters: the encoding's glyph names, then the font's own /ToUnicode.
    if !f.composite {
        let mut enc = Rng::default();
        if dict_get(&r.data, fd, "/Encoding", &mut enc) && deref(r, &mut enc) && is_dict(&r.data, enc) {
            let mut diffs = Rng::default();
            if dict_get(&r.data, enc, "/Differences", &mut diffs) && deref(r, &mut diffs) && is_array(&r.data, diffs) {
                let e = diffs.e - 1;
                let mut p = diffs.p + 1;
                let mut it = Rng::default();
                let mut code = 0i32;
                while arr_next(&r.data, &mut p, e, &mut it) {
                    let mut n = 0i64;
                    if span_long(&r.data, it, &mut n) {
                        code = n as i32;
                        continue;
                    }
                    let mut nm = String::new();
                    span_name(&r.data, it, &mut nm, 40);
                    if nm.is_empty() {
                        continue;
                    }
                    if let Some(u) = glyph_name_unicode(&nm) {
                        f.uni.push((code as u32, u));
                    }
                    code += 1;
                }
            }
        }
    }
    let mut tu = Rng::default();
    if dict_get(&r.data, fd, "/ToUnicode", &mut tu) {
        let mut num = 0;
        if ref_num(&r.data, tu, &mut num) {
            let mut dv = Rng::default();
            let mut s = None;
            let mut streamed = false;
            if obj_parse(r, obj_find(r, num), &mut dv, &mut s, &mut streamed) {
                if let Some(s) = s {
                    if let Some(cm) = stream_data(r, dv, s, PDF_MAX_CMAP) {
                        load_cmap(&cm, &mut f.uni);
                    }
                }
            }
        }
    }
    if f.composite {
        let mut cm = Rng::default();
        if dict_get(&r.data, desc, "/CIDToGIDMap", &mut cm) {
            let mut num = 0;
            if ref_num(&r.data, cm, &mut num) {
                let mut dv = Rng::default();
                let mut s = None;
                let mut streamed = false;
                if obj_parse(r, obj_find(r, num), &mut dv, &mut s, &mut streamed) {
                    if let Some(s) = s {
                        f.cid2gid = stream_data(r, dv, s, PDF_MAX_CMAP);
                    }
                }
            }
        }
    }
    f
}

// A /W array: "c [w1 w2 ...]" and "first last w", in either order.
fn cid_widths(r: &PdfReader, w: Rng, out: &mut Vec<(i32, i32, f32)>) {
    let e = w.e - 1;
    let mut p = w.p + 1;
    let mut it = Rng::default();
    let mut items: Vec<Rng> = Vec::new();
    while items.len() < 4096 && arr_next(&r.data, &mut p, e, &mut it) {
        items.push(it);
    }
    let mut i = 0usize;
    while i < items.len() {
        let mut c = 0i64;
        if !span_long(&r.data, items[i], &mut c) {
            break;
        }
        i += 1;
        if i >= items.len() {
            break;
        }
        if is_array(&r.data, items[i]) {
            let a = items[i];
            let ae = a.e - 1;
            let mut ap = a.p + 1;
            let mut ai = Rng::default();
            let mut cid = c as i32;
            while arr_next(&r.data, &mut ap, ae, &mut ai) {
                out.push((cid, cid, span_f32(&r.data, ai).unwrap_or(0.0)));
                cid += 1;
            }
            i += 1;
            continue;
        }
        let mut hi = 0i64;
        if !span_long(&r.data, items[i], &mut hi) {
            break;
        }
        i += 1;
        if i >= items.len() {
            break;
        }
        out.push((c as i32, hi as i32, span_f32(&r.data, items[i]).unwrap_or(0.0)));
        i += 1;
    }
}

// A /ToUnicode CMap's bfchar and bfrange entries into out (later entries win: unicode_of reads
// the list backwards).
fn load_cmap(d: &[u8], out: &mut Vec<(u32, u32)>) {
    let e = d.len();
    let mut i = 0usize;
    while i < e {
        if let Some(at) = find_bytes(d, i, e, b"beginbfchar") {
            let mut p = at + 11;
            let stop = find_bytes(d, p, e, b"endbfchar").unwrap_or(e);
            while let Some(src) = next_hex(d, &mut p, stop) {
                let Some(dst) = next_hex(d, &mut p, stop) else { break };
                out.push((hex_code(&src), hex_code(&dst)));
            }
            i = stop;
        } else if let Some(at) = find_bytes(d, i, e, b"beginbfrange") {
            let mut p = at + 12;
            let stop = find_bytes(d, p, e, b"endbfrange").unwrap_or(e);
            loop {
                let Some(lo) = next_hex(d, &mut p, stop) else { break };
                let Some(hi) = next_hex(d, &mut p, stop) else { break };
                let (lo, hi) = (hex_code(&lo), hex_code(&hi));
                let q = skip_ws(d, p, stop);
                if q < stop && d[q] == b'[' {
                    let ae = array_end(d, q, stop);
                    let mut ip = q + 1;
                    let mut code = lo;
                    while code <= hi {
                        let Some(dst) = next_hex(d, &mut ip, ae) else { break };
                        out.push((code, hex_code(&dst)));
                        code += 1;
                    }
                    p = ae;
                } else if let Some(dst) = next_hex(d, &mut p, stop) {
                    let base = hex_code(&dst);
                    let mut code = lo;
                    while code <= hi {
                        out.push((code, base.wrapping_add(code - lo)));
                        code += 1;
                    }
                } else {
                    break;
                }
            }
            i = stop;
        } else {
            break;
        }
    }
}

// The next <hex> string at p, past its '>'.
fn next_hex(d: &[u8], p: &mut usize, e: usize) -> Option<Vec<u8>> {
    let mut q = *p;
    loop {
        let at = find_bytes(d, q, e, b"<")?;
        if at + 1 < e && d[at + 1] == b'<' {
            q = at + 2;
            continue;
        }
        let end = find_bytes(d, at + 1, e, b">")?;
        let bytes = hex_bytes(&d[at + 1..end]);
        *p = end + 1;
        return Some(bytes);
    }
}

fn hex_bytes(s: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut hi: i32 = -1;
    for &c in s {
        let v = match c {
            b'0'..=b'9' => (c - b'0') as i32,
            b'a'..=b'f' => (c - b'a') as i32 + 10,
            b'A'..=b'F' => (c - b'A') as i32 + 10,
            _ => continue,
        };
        if hi < 0 {
            hi = v;
        } else {
            out.push((hi * 16 + v) as u8);
            hi = -1;
        }
    }
    if hi >= 0 {
        out.push((hi * 16) as u8);
    }
    out
}

// A CMap destination's character: up to four bytes (UTF-16BE), surrogate pairs joined.
fn hex_code(b: &[u8]) -> u32 {
    if b.len() >= 4 {
        let hi = ((b[0] as u32) << 8) | b[1] as u32;
        let lo = ((b[2] as u32) << 8) | b[3] as u32;
        if (0xD800..0xDC00).contains(&hi) && (0xDC00..0xE000).contains(&lo) {
            return 0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00);
        }
    }
    let mut v: u32 = 0;
    for &x in b.iter().take(4) {
        v = (v << 8) | x as u32;
    }
    v
}

// A Symbol font's characters are in the Private Use Area (its /ToUnicode says F020 for the space,
// F030 for the zero): the same character sits F000 lower, where a face's own glyphs are, so neither
// Grimoire's face nor a text face's cmap is asked for an icon there.
fn char_of(u: u32) -> u32 {
    if (0xF020..=0xF0FF).contains(&u) { u - 0xF000 } else { u }
}

// A format 4 cmap mapping 0x20 to 0xFF to the same glyph ids (a Symbol font's codes, shifted):
// the smallest table stb_truetype takes.
fn build_cmap() -> Vec<u8> {
    let seg: u16 = 2; // (the range, and the 0xFFFF that ends the table)
    let len: u16 = 14 + 8 * seg + 2;
    let mut sub: Vec<u8> = Vec::with_capacity(32);
    sub.extend_from_slice(&4u16.to_be_bytes());
    sub.extend_from_slice(&len.to_be_bytes());
    sub.extend_from_slice(&0u16.to_be_bytes()); // language
    sub.extend_from_slice(&(seg * 2).to_be_bytes());
    sub.extend_from_slice(&4u16.to_be_bytes()); // searchRange
    sub.extend_from_slice(&1u16.to_be_bytes()); // entrySelector
    sub.extend_from_slice(&0u16.to_be_bytes()); // rangeShift
    sub.extend_from_slice(&0xFFu16.to_be_bytes()); // endCode
    sub.extend_from_slice(&0xFFFFu16.to_be_bytes());
    sub.extend_from_slice(&0u16.to_be_bytes()); // reservedPad
    sub.extend_from_slice(&0x20u16.to_be_bytes()); // startCode
    sub.extend_from_slice(&0xFFFFu16.to_be_bytes());
    sub.extend_from_slice(&0u16.to_be_bytes()); // idDelta: glyph id = code
    sub.extend_from_slice(&1u16.to_be_bytes());
    sub.extend_from_slice(&0u16.to_be_bytes()); // idRangeOffset
    sub.extend_from_slice(&0u16.to_be_bytes());
    let mut out: Vec<u8> = Vec::with_capacity(44);
    out.extend_from_slice(&0u16.to_be_bytes()); // version
    out.extend_from_slice(&1u16.to_be_bytes()); // one encoding
    out.extend_from_slice(&3u16.to_be_bytes()); // platform: Windows
    out.extend_from_slice(&1u16.to_be_bytes()); // encoding: Unicode BMP
    out.extend_from_slice(&12u32.to_be_bytes());
    out.extend_from_slice(&sub);
    out
}

// The program with a cmap table added (see build_cmap): its table directory grows by one record,
// and every table in it moves up the 16 bytes that record takes. stb_truetype reads the directory
// and the tables; it checks no checksum.
fn with_cmap(prog: &[u8]) -> Option<Vec<u8>> {
    if prog.len() < 12 {
        return None;
    }
    let n = u16::from_be_bytes([prog[4], prog[5]]) as usize;
    if n == 0 || n > 64 || prog.len() < 12 + 16 * n {
        return None;
    }
    let base = 12 + 16 * n;
    let cmap = build_cmap();
    let mut out: Vec<u8> = Vec::new();
    out.try_reserve_exact(prog.len() + 16 + cmap.len()).ok()?;
    out.extend_from_slice(&prog[..4]); // sfnt version
    out.extend_from_slice(&((n as u16) + 1).to_be_bytes());
    out.extend_from_slice(&[0u8; 6]); // searchRange, entrySelector, rangeShift (unread here)
    for i in 0..n {
        let r = &prog[12 + 16 * i..12 + 16 * i + 16];
        out.extend_from_slice(&r[..8]);
        let off = u32::from_be_bytes([r[8], r[9], r[10], r[11]]);
        out.extend_from_slice(&(off + 16).to_be_bytes());
        out.extend_from_slice(&r[12..16]);
    }
    out.extend_from_slice(b"cmap");
    out.extend_from_slice(&0u32.to_be_bytes());
    out.extend_from_slice(&((prog.len() as u32) + 16).to_be_bytes());
    out.extend_from_slice(&(cmap.len() as u32).to_be_bytes());
    out.extend_from_slice(&prog[base..]);
    out.extend_from_slice(&cmap);
    Some(out)
}

// The character a glyph name stands for: the name itself for a letter, "uni0041", "u1F600", and
// the handful of names type sets often (a subset font's codes otherwise come from /ToUnicode).
fn glyph_name_unicode(name: &str) -> Option<u32> {
    if name.len() == 1 {
        let c = name.as_bytes()[0];
        if c > 32 && c < 127 {
            return Some(c as u32);
        }
    }
    if let Some(hex) = name.strip_prefix("uni") {
        if hex.len() >= 4 {
            return u32::from_str_radix(&hex[..4], 16).ok();
        }
    }
    if let Some(hex) = name.strip_prefix('u') {
        if (4..=6).contains(&hex.len()) {
            return u32::from_str_radix(hex, 16).ok();
        }
    }
    const NAMED: [(&str, u32); 61] = [
        ("space", 32),
        ("exclam", 33),
        ("quotedbl", 34),
        ("numbersign", 35),
        ("dollar", 36),
        ("percent", 37),
        ("ampersand", 38),
        ("quotesingle", 39),
        ("parenleft", 40),
        ("parenright", 41),
        ("asterisk", 42),
        ("plus", 43),
        ("comma", 44),
        ("hyphen", 45),
        ("period", 46),
        ("slash", 47),
        ("zero", 48),
        ("one", 49),
        ("two", 50),
        ("three", 51),
        ("four", 52),
        ("five", 53),
        ("six", 54),
        ("seven", 55),
        ("eight", 56),
        ("nine", 57),
        ("colon", 58),
        ("semicolon", 59),
        ("less", 60),
        ("equal", 61),
        ("greater", 62),
        ("question", 63),
        ("at", 64),
        ("bracketleft", 91),
        ("backslash", 92),
        ("bracketright", 93),
        ("asciicircum", 94),
        ("underscore", 95),
        ("grave", 96),
        ("braceleft", 123),
        ("bar", 124),
        ("braceright", 125),
        ("asciitilde", 126),
        ("quoteright", 0x2019),
        ("quoteleft", 0x2018),
        ("quotedblleft", 0x201C),
        ("quotedblright", 0x201D),
        ("endash", 0x2013),
        ("emdash", 0x2014),
        ("bullet", 0x2022),
        ("ellipsis", 0x2026),
        ("fi", 0xFB01),
        ("fl", 0xFB02),
        ("ff", 0xFB00),
        ("minus", 0x2212),
        ("degree", 0xB0),
        ("section", 0xA7),
        ("paragraph", 0xB6),
        ("germandbls", 0xDF),
        ("nbspace", 0xA0),
        ("copyright", 0xA9),
    ];
    NAMED.iter().find(|(n, _)| *n == name).map(|&(_, u)| u)
}

// The graphics and text state, saved and restored by q and Q.
#[derive(Clone)]
struct PgState {
    ctm: Mat6,
    clip: RectI,
    lw: f32,
    fill: [u8; 3],
    stroke: [u8; 3],
    alpha: f32,
    stroke_alpha: f32,
    cfill: Color,
    cstroke: Color,
    font: Option<Rc<PdfFont>>,
    size: f32,
    tc: f32,
    tw: f32,
    th: f32,
    tl: f32,
    rise: f32,
    mode: i32,
    tm: Mat6,
    tlm: Mat6,
    res: Rng,
}

fn pg_state(ctm: Mat6, clip: RectI, res: Rng) -> PgState {
    PgState {
        ctm,
        clip,
        lw: 1.0,
        fill: [0, 0, 0],
        stroke: [0, 0, 0],
        alpha: 1.0,
        stroke_alpha: 1.0,
        cfill: Color::default(),
        cstroke: Color::default(),
        font: None,
        size: 0.0,
        tc: 0.0,
        tw: 0.0,
        th: 1.0,
        tl: 0.0,
        rise: 0.0,
        mode: 0,
        tm: mat_id(),
        tlm: mat_id(),
        res,
    }
}

/// Grimoire's own face, for text whose font program is not TrueType (or is missing).
struct Fallback {
    info: Box<ffi_stb::stbtt_fontinfo>,
    em: f32,
}

/// The page being drawn: the canvas, the state, and the page's fonts.
struct PgCtx<'a> {
    r: &'a PdfReader,
    canvas: Canvas3,
    gs: PgState,
    stack: Vec<PgState>,
    path: PgPath,
    clip_pending: bool,
    fonts: HashMap<String, Rc<PdfFont>>,
    fallback: Option<Fallback>,
    depth: i32,
}

impl<'a> PgCtx<'a> {
    fn new(r: &'a PdfReader, canvas: Canvas3, base: Mat6, res: Rng) -> PgCtx<'a> {
        let clip = RectI::whole(canvas.w as i32, canvas.h as i32);
        let mut fallback = None;
        let mut info = Box::new(ffi_stb::stbtt_fontinfo::default());
        // SAFETY: Terminess is a TrueType face compiled into the binary.
        let off = unsafe { ffi_stb::stbtt_GetFontOffsetForIndex(FONT_TERMINESS_REGULAR.as_ptr(), 0) };
        if off >= 0 && unsafe { ffi_stb::stbtt_InitFont(&mut *info, FONT_TERMINESS_REGULAR.as_ptr(), off) } != 0 {
            // SAFETY: info was just initialized from that face.
            let em = unsafe { ffi_stb::stbtt_ScaleForMappingEmToPixels(&*info, 1.0) };
            fallback = Some(Fallback { info, em: if em > 0.0 && em.is_finite() { em } else { 0.001 } });
        }
        PgCtx {
            r,
            canvas,
            gs: pg_state(base, clip, res),
            stack: Vec::new(),
            path: PgPath::default(),
            clip_pending: false,
            fonts: HashMap::new(),
            fallback,
            depth: 0,
        }
    }

    fn dev(&self, x: f32, y: f32) -> (f32, f32) {
        mat_pt(&self.gs.ctm, x, y)
    }

    fn eff_clip(&self) -> RectI {
        if self.clip_pending {
            self.gs.clip.clip_to(self.path.bbox_rect(self.gs.clip))
        } else {
            self.gs.clip
        }
    }

    fn finish_path(&mut self) {
        if self.clip_pending {
            let r = self.path.bbox_rect(self.gs.clip);
            self.gs.clip = self.gs.clip.clip_to(r);
            self.clip_pending = false;
        }
        self.path.reset();
    }

    fn fill_path(&mut self, even_odd: bool) {
        if self.path.sub.is_empty() {
            return;
        }
        let clip = self.eff_clip();
        fill_polys(&mut self.canvas, &self.path.sub, self.gs.fill, self.gs.alpha, even_odd, clip);
    }

    fn stroke_path(&mut self) {
        if self.path.sub.is_empty() {
            return;
        }
        let clip = self.eff_clip();
        let lw = (self.gs.lw * mat_scale(&self.gs.ctm)).max(0.6);
        stroke_polys(&mut self.canvas, &self.path.sub, lw, self.gs.stroke, self.gs.stroke_alpha, clip);
    }

    fn font_for(&mut self, name: &str) -> Rc<PdfFont> {
        if let Some(f) = self.fonts.get(name) {
            return f.clone();
        }
        let res = self.gs.res;
        let key = format!("/{name}");
        let mut fd = Rng::default();
        let mut found = false;
        if !res.is_null() {
            let mut fonts = Rng::default();
            if dict_get(&self.r.data, res, "/Font", &mut fonts) && deref(self.r, &mut fonts) {
                let mut v = Rng::default();
                if dict_get(&self.r.data, fonts, &key, &mut v) && deref(self.r, &mut v) && is_dict(&self.r.data, v) {
                    fd = v;
                    found = true;
                }
            }
        }
        let f = if found { load_font(self.r, fd) } else { PdfFont::plain() };
        let rc = Rc::new(f);
        self.fonts.insert(name.to_string(), rc.clone());
        rc
    }

    fn named_colorspace(&self, name: &str, out: &mut Color) -> bool {
        *out = Color::default();
        match name {
            "DeviceGray" | "G" | "CalGray" => {
                out.comps = CS_GRAY;
                out.kind = CS_GRAY;
                return true;
            }
            "DeviceRGB" | "RGB" | "CalRGB" => {
                out.comps = CS_RGB;
                out.kind = CS_RGB;
                return true;
            }
            "DeviceCMYK" | "CMYK" => {
                out.comps = 4;
                out.kind = CS_CMYK;
                return true;
            }
            "Pattern" => return false,
            _ => {}
        }
        if self.gs.res.is_null() {
            return false;
        }
        let mut dict = Rng::default();
        if !dict_get(&self.r.data, self.gs.res, "/ColorSpace", &mut dict) || !deref(self.r, &mut dict) {
            return false;
        }
        let key = format!("/{name}");
        let mut v = Rng::default();
        if !dict_get(&self.r.data, dict, &key, &mut v) {
            return false;
        }
        colorspace(self.r, v, out)
    }

    fn ext_gstate(&mut self, name: &str) {
        let res = self.gs.res;
        if res.is_null() {
            return;
        }
        let key = format!("/{name}");
        let mut ges = Rng::default();
        if !dict_get(&self.r.data, res, "/ExtGState", &mut ges) || !deref(self.r, &mut ges) {
            return;
        }
        let mut dv = Rng::default();
        if !dict_get(&self.r.data, ges, &key, &mut dv) || !deref(self.r, &mut dv) || !is_dict(&self.r.data, dv) {
            return;
        }
        if let Some(x) = dict_f32(self.r, dv, "/ca") {
            self.gs.alpha = clamp01(x);
        }
        if let Some(x) = dict_f32(self.r, dv, "/CA") {
            self.gs.stroke_alpha = clamp01(x);
        }
        if let Some(x) = dict_f32(self.r, dv, "/LW") {
            self.gs.lw = x;
        }
    }

    fn next_line(&mut self) {
        let ty = -self.gs.tl;
        self.gs.tlm = mat_mul(&self.gs.tlm, &[1.0, 0.0, 0.0, 1.0, 0.0, ty]);
        self.gs.tm = self.gs.tlm;
    }

    fn show(&mut self, bytes: &[u8]) {
        let Some(font) = self.gs.font.clone() else { return };
        let fs = self.gs.size;
        if !fs.is_finite() || fs == 0.0 {
            return;
        }
        let mut i = 0usize;
        while i < bytes.len() {
            let code = if font.composite {
                if i + 1 >= bytes.len() {
                    break;
                }
                let c = ((bytes[i] as u32) << 8) | bytes[i + 1] as u32;
                i += 2;
                c
            } else {
                let c = bytes[i] as u32;
                i += 1;
                c
            };
            let mut adv = font.width(code) / 1000.0 * fs;
            adv += self.gs.tc;
            if code == 32 {
                adv += self.gs.tw;
            }
            self.draw_glyph(&font, code);
            let tx = adv * self.gs.th;
            if tx.is_finite() && tx != 0.0 {
                self.gs.tm = mat_mul(&self.gs.tm, &[1.0, 0.0, 0.0, 1.0, tx, 0.0]);
            }
        }
    }

    fn draw_glyph(&mut self, f: &PdfFont, code: u32) {
        let mode = self.gs.mode;
        let fill_it = matches!(mode, 0 | 2 | 4 | 6);
        let stroke_it = matches!(mode, 1 | 2 | 5 | 6);
        if !fill_it && !stroke_it {
            return;
        }
        let m = mat_mul(&self.gs.ctm, &self.gs.tm);
        let gm = mat_mul(
            &m,
            &[self.gs.size * self.gs.th, 0.0, 0.0, self.gs.size, 0.0, self.gs.rise],
        );
        let mut path = PgPath::default();
        let mut ok = false;
        if let Some(info) = f.info.as_deref() {
            if let Some(gid) = f.gid(code) {
                ok = glyph_polys(&mut path, info, gid, f.em, &gm);
            }
        }
        if !ok {
            let cp = char_of(f.unicode_of(code));
            if let Some(fb) = self.fallback.as_ref() {
                // SAFETY: fb.info is an initialized Terminess face.
                let gid = unsafe { ffi_stb::stbtt_FindGlyphIndex(&*fb.info, cp as i32) };
                if gid > 0 {
                    // Grimoire's face is monospaced; the PDF's font (not embedded, or CFF) is
                    // usually not, and its widths are what place the letters. The glyph is drawn
                    // as wide as the advance the PDF gives it, so a narrow letter keeps its slot
                    // instead of running into the next.
                    let (mut nat, mut _lsb) = (0i32, 0i32);
                    // SAFETY: gid is a glyph of fb.info.
                    unsafe { ffi_stb::stbtt_GetGlyphHMetrics(&*fb.info, gid, &mut nat, &mut _lsb) };
                    let natural = nat as f32 * fb.em;
                    let want = f.width(code) / 1000.0;
                    let sx = if natural > 0.0001 && want > 0.0 {
                        (want / natural).clamp(0.4, 2.5)
                    } else {
                        1.0
                    };
                    let gms = mat_mul(
                        &m,
                        &[self.gs.size * self.gs.th * sx, 0.0, 0.0, self.gs.size, 0.0, self.gs.rise],
                    );
                    ok = glyph_polys(&mut path, &fb.info, gid, fb.em, &gms);
                }
            }
        }
        if !ok || path.sub.is_empty() {
            return;
        }
        let clip = self.gs.clip;
        if fill_it {
            fill_polys(&mut self.canvas, &path.sub, self.gs.fill, self.gs.alpha, false, clip);
        }
        if stroke_it {
            let lw = (self.gs.lw * mat_scale(&m)).max(0.6);
            stroke_polys(&mut self.canvas, &path.sub, lw, self.gs.stroke, self.gs.stroke_alpha, clip);
        }
    }

    fn do_xobject(&mut self, name: &str) {
        let r = self.r;
        let res = self.gs.res;
        if res.is_null() {
            return;
        }
        let key = format!("/{name}");
        let mut xo = Rng::default();
        if !dict_get(&r.data, res, "/XObject", &mut xo) || !deref(r, &mut xo) {
            return;
        }
        let mut v = Rng::default();
        if !dict_get(&r.data, xo, &key, &mut v) {
            return;
        }
        let mut num = 0;
        if !ref_num(&r.data, v, &mut num) {
            return;
        }
        let mut dv = Rng::default();
        let mut s = None;
        let mut streamed = false;
        if !obj_parse(r, obj_find(r, num), &mut dv, &mut s, &mut streamed) {
            return;
        }
        let mut sub = String::new();
        dict_name(r, dv, "/Subtype", &mut sub, 24);
        if sub == "Image" {
            let Some(s) = s else { return };
            let mut pic = BgPicture::default();
            let mut why = String::new();
            if decode_image(r, &dv, &s, &mut pic, &mut why) == PDF_OK {
                draw_pic(&mut self.canvas, &pic, &self.gs.ctm, self.gs.clip);
            }
            bgpicture_free(&mut pic);
        } else if sub == "Form" {
            let Some(s) = s else { return };
            if self.depth >= 8 {
                return;
            }
            let Some(data) = stream_data(r, dv, s, PDF_MAX_CONTENT) else { return };
            let mut m = mat_id();
            let mut mv = Rng::default();
            if dict_get(&r.data, dv, "/Matrix", &mut mv) && deref(r, &mut mv) {
                let mut a = [0f32; 8];
                if array_nums(&r.data, mv, &mut a) >= 6 {
                    m = [a[0], a[1], a[2], a[3], a[4], a[5]];
                }
            }
            let ctm = mat_mul(&self.gs.ctm, &m);
            let mut clip = self.gs.clip;
            let mut bv = Rng::default();
            let mut b = [0f32; 8];
            if dict_get(&r.data, dv, "/BBox", &mut bv) && deref(r, &mut bv) && array_nums(&r.data, bv, &mut b) >= 4 {
                clip = bbox_clip(&ctm, [b[0], b[1], b[2], b[3]], clip);
            }
            let saved = self.gs.clone();
            self.gs.ctm = ctm;
            self.gs.clip = clip;
            let mut fres = Rng::default();
            if dict_get(&r.data, dv, "/Resources", &mut fres) && deref(r, &mut fres) {
                self.gs.res = fres;
            }
            self.depth += 1;
            self.run(&data);
            self.depth -= 1;
            self.gs = saved;
        }
    }

    fn op(&mut self, op: &str, ops: &[Opnd]) {
        match op {
            "q" => {
                if self.stack.len() < 64 {
                    let g = self.gs.clone();
                    self.stack.push(g);
                }
            }
            "Q" => {
                if let Some(g) = self.stack.pop() {
                    self.gs = g;
                }
            }
            "cm" => {
                let m: Mat6 = [on(ops, 0), on(ops, 1), on(ops, 2), on(ops, 3), on(ops, 4), on(ops, 5)];
                self.gs.ctm = mat_mul(&self.gs.ctm, &m);
            }
            "w" => {
                let v = on(ops, 0);
                if v.is_finite() && v >= 0.0 {
                    self.gs.lw = v;
                }
            }
            "gs" => {
                let nm = oname(ops, 0);
                self.ext_gstate(&nm);
            }
            "m" => {
                let p = self.dev(on(ops, 0), on(ops, 1));
                self.path.move_to(p.0, p.1);
            }
            "l" => {
                let p = self.dev(on(ops, 0), on(ops, 1));
                self.path.line_to(p.0, p.1);
            }
            "c" => {
                let a = self.dev(on(ops, 0), on(ops, 1));
                let b = self.dev(on(ops, 2), on(ops, 3));
                let p = self.dev(on(ops, 4), on(ops, 5));
                self.path.cubic_to(a, b, p);
            }
            "v" => {
                let b = self.dev(on(ops, 0), on(ops, 1));
                let p = self.dev(on(ops, 2), on(ops, 3));
                let a = self.path.last.unwrap_or(b);
                self.path.cubic_to(a, b, p);
            }
            "y" => {
                let a = self.dev(on(ops, 0), on(ops, 1));
                let p = self.dev(on(ops, 2), on(ops, 3));
                self.path.cubic_to(a, p, p);
            }
            "h" => self.path.close(),
            "re" => {
                let (x, y, w, h) = (on(ops, 0), on(ops, 1), on(ops, 2), on(ops, 3));
                let a = self.dev(x, y);
                let b = self.dev(x + w, y);
                let c = self.dev(x + w, y + h);
                let d = self.dev(x, y + h);
                self.path.move_to(a.0, a.1);
                self.path.line_to(b.0, b.1);
                self.path.line_to(c.0, c.1);
                self.path.line_to(d.0, d.1);
                self.path.close();
            }
            "S" => {
                self.path.done();
                self.stroke_path();
                self.finish_path();
            }
            "s" => {
                self.path.close();
                self.path.done();
                self.stroke_path();
                self.finish_path();
            }
            "f" | "F" => {
                self.path.done();
                self.fill_path(false);
                self.finish_path();
            }
            "f*" => {
                self.path.done();
                self.fill_path(true);
                self.finish_path();
            }
            "B" => {
                self.path.done();
                self.fill_path(false);
                self.stroke_path();
                self.finish_path();
            }
            "B*" => {
                self.path.done();
                self.fill_path(true);
                self.stroke_path();
                self.finish_path();
            }
            "b" => {
                self.path.close();
                self.path.done();
                self.fill_path(false);
                self.stroke_path();
                self.finish_path();
            }
            "b*" => {
                self.path.close();
                self.path.done();
                self.fill_path(true);
                self.stroke_path();
                self.finish_path();
            }
            "n" => self.finish_path(),
            "W" | "W*" => self.clip_pending = true,
            "g" => self.gs.fill = gray8(on(ops, 0)),
            "G" => self.gs.stroke = gray8(on(ops, 0)),
            "rg" => self.gs.fill = rgb8(on(ops, 0), on(ops, 1), on(ops, 2)),
            "RG" => self.gs.stroke = rgb8(on(ops, 0), on(ops, 1), on(ops, 2)),
            "k" => self.gs.fill = cmyk8(on(ops, 0), on(ops, 1), on(ops, 2), on(ops, 3)),
            "K" => self.gs.stroke = cmyk8(on(ops, 0), on(ops, 1), on(ops, 2), on(ops, 3)),
            "cs" | "CS" => {
                let nm = oname(ops, 0);
                let mut c = Color::default();
                let ok = self.named_colorspace(&nm, &mut c);
                if op == "cs" {
                    self.gs.cfill = if ok { c } else { Color::default() };
                } else {
                    self.gs.cstroke = if ok { c } else { Color::default() };
                }
            }
            "sc" | "scn" | "SC" | "SCN" => {
                let stroke = op == "SC" || op == "SCN";
                let cs = if stroke { self.gs.cstroke.clone() } else { self.gs.cfill.clone() };
                set_colour(&cs, ops, stroke, &mut self.gs);
            }
            "BT" => {
                self.gs.tm = mat_id();
                self.gs.tlm = mat_id();
            }
            "Tf" => {
                let nm = oname(ops, 0);
                let f = self.font_for(&nm);
                self.gs.font = Some(f);
                self.gs.size = on(ops, 1);
            }
            "Td" => {
                let (tx, ty) = (on(ops, 0), on(ops, 1));
                self.gs.tlm = mat_mul(&self.gs.tlm, &[1.0, 0.0, 0.0, 1.0, tx, ty]);
                self.gs.tm = self.gs.tlm;
            }
            "TD" => {
                let (tx, ty) = (on(ops, 0), on(ops, 1));
                self.gs.tl = -ty;
                self.gs.tlm = mat_mul(&self.gs.tlm, &[1.0, 0.0, 0.0, 1.0, tx, ty]);
                self.gs.tm = self.gs.tlm;
            }
            "Tm" => {
                self.gs.tm = [on(ops, 0), on(ops, 1), on(ops, 2), on(ops, 3), on(ops, 4), on(ops, 5)];
                self.gs.tlm = self.gs.tm;
            }
            "T*" => self.next_line(),
            "TL" => self.gs.tl = on(ops, 0),
            "Tc" => self.gs.tc = on(ops, 0),
            "Tw" => self.gs.tw = on(ops, 0),
            "Tz" => {
                let v = on(ops, 0);
                if v.is_finite() {
                    self.gs.th = v / 100.0;
                }
            }
            "Ts" => self.gs.rise = on(ops, 0),
            "Tr" => {
                let v = on(ops, 0);
                if v.is_finite() {
                    self.gs.mode = v as i32;
                }
            }
            "Tj" => {
                let s = ostr(ops, 0);
                self.show(&s);
            }
            "TJ" => {
                if let Some(Opnd::Arr(items)) = ops.first() {
                    for it in items {
                        match it {
                            Opnd::Str(s) => self.show(s),
                            Opnd::Num(v) => {
                                let tx = -v / 1000.0 * self.gs.size * self.gs.th;
                                if tx.is_finite() {
                                    self.gs.tm = mat_mul(&self.gs.tm, &[1.0, 0.0, 0.0, 1.0, tx, 0.0]);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            "'" => {
                self.next_line();
                let s = ostr(ops, 0);
                self.show(&s);
            }
            "\"" => {
                self.gs.tw = on(ops, 0);
                self.gs.tc = on(ops, 1);
                self.next_line();
                let s = ostr(ops, 2);
                self.show(&s);
            }
            "Do" => {
                let nm = oname(ops, 0);
                self.do_xobject(&nm);
            }
            _ => {}
        }
    }

    fn run(&mut self, data: &[u8]) {
        let e = data.len();
        let mut p = 0usize;
        let mut ops: Vec<Opnd> = Vec::new();
        let mut guard = 0usize;
        while p < e {
            guard += 1;
            if guard > 4_000_000 {
                break;
            }
            let start = p;
            if let Some(v) = content_operand(data, &mut p, e, 0) {
                if ops.len() < 64 {
                    ops.push(v);
                }
                continue;
            }
            if p != start {
                ops.clear();
                continue;
            }
            let q = skip_ws(data, p, e);
            if q >= e {
                break;
            }
            let ke = tok_end(data, q, e);
            if ke <= q {
                p = q + 1;
                ops.clear();
                continue;
            }
            let len = ke - q;
            let name = if len <= 32 {
                std::str::from_utf8(&data[q..ke]).unwrap_or("").to_string()
            } else {
                String::new()
            };
            p = ke;
            if name == "BI" {
                p = skip_inline(data, p, e);
                ops.clear();
                continue;
            }
            if !name.is_empty() {
                self.op(&name, &ops);
            }
            ops.clear();
        }
    }
}

// A colour from sc/scn (or SC/SCN) in the current colour space.
fn set_colour(cs: &Color, ops: &[Opnd], stroke: bool, st: &mut PgState) {
    let nums: Vec<f32> = ops
        .iter()
        .filter_map(|o| if let Opnd::Num(v) = o { Some(*v) } else { None })
        .collect();
    let n = nums.len();
    let rgb = if !cs.pal.is_empty() {
        let idx = nums.first().copied().unwrap_or(0.0).max(0.0) as usize;
        let step = cs.palcomp.max(1) as usize;
        let at = idx.saturating_mul(step);
        if at + step <= cs.pal.len() {
            if step == 1 {
                [cs.pal[at], cs.pal[at], cs.pal[at]]
            } else {
                [cs.pal[at], cs.pal[at + 1], cs.pal[at + 2]]
            }
        } else {
            [0, 0, 0]
        }
    } else if cs.comps == 1 || (cs.comps == 0 && n == 1) {
        gray8(nums.first().copied().unwrap_or(0.0))
    } else if cs.comps == 4 || (cs.comps == 0 && n == 4) {
        cmyk8(
            nums.first().copied().unwrap_or(0.0),
            nums.get(1).copied().unwrap_or(0.0),
            nums.get(2).copied().unwrap_or(0.0),
            nums.get(3).copied().unwrap_or(0.0),
        )
    } else {
        let r = nums.first().copied().unwrap_or(0.0);
        let g = nums.get(1).copied().unwrap_or(r);
        let b = nums.get(2).copied().unwrap_or(r);
        rgb8(r, g, b)
    };
    if stroke {
        st.stroke = rgb;
    } else {
        st.fill = rgb;
    }
}

// The rectangle a form's /BBox covers, through its matrix and the CTM.
fn bbox_clip(m: &Mat6, b: [f32; 4], clip: RectI) -> RectI {
    let mut x0 = f32::MAX;
    let mut y0 = f32::MAX;
    let mut x1 = f32::MIN;
    let mut y1 = f32::MIN;
    for (x, y) in [(b[0], b[1]), (b[2], b[1]), (b[2], b[3]), (b[0], b[3])] {
        let (dx, dy) = mat_pt(m, x, y);
        if !dx.is_finite() || !dy.is_finite() {
            return clip;
        }
        x0 = x0.min(dx);
        y0 = y0.min(dy);
        x1 = x1.max(dx);
        y1 = y1.max(dy);
    }
    RectI {
        x0: (x0.floor() as i32).saturating_sub(1),
        y0: (y0.floor() as i32).saturating_sub(1),
        x1: (x1.ceil() as i32).saturating_add(1),
        y1: (y1.ceil() as i32).saturating_add(1),
    }
    .clip_to(clip)
}

// One source pixel of a picture as RGB (a gray picture is its own three).
fn pic_px(p: &BgPicture, x: i32, y: i32) -> [u8; 3] {
    let x = x.clamp(0, p.w - 1) as usize;
    let y = y.clamp(0, p.h - 1) as usize;
    let ch = p.ch.max(1) as usize;
    let i = (y * p.w as usize + x) * ch;
    if ch == 1 {
        let v = p.px[i];
        [v, v, v]
    } else {
        [p.px[i], p.px[i + 1], p.px[i + 2]]
    }
}

// A picture sampled at (sx, sy) source pixels, over a footprint of fu x fv: bilinear when it is
// close to one pixel, an area average when it is more (a big picture shrunk into the page).
fn pic_sample(p: &BgPicture, sx: f32, sy: f32, fu: f32, fv: f32) -> [u8; 3] {
    if fu <= 1.5 && fv <= 1.5 {
        let x = sx - 0.5;
        let y = sy - 0.5;
        let x0 = x.floor();
        let y0 = y.floor();
        let tx = x - x0;
        let ty = y - y0;
        let (x0, y0) = (x0 as i32, y0 as i32);
        let a = pic_px(p, x0, y0);
        let b = pic_px(p, x0 + 1, y0);
        let c = pic_px(p, x0, y0 + 1);
        let d = pic_px(p, x0 + 1, y0 + 1);
        let mut o = [0u8; 3];
        for i in 0..3 {
            let t = a[i] as f32 * (1.0 - tx) + b[i] as f32 * tx;
            let u = c[i] as f32 * (1.0 - tx) + d[i] as f32 * tx;
            o[i] = (t * (1.0 - ty) + u * ty + 0.5) as u8;
        }
        return o;
    }
    let nu = (fu.ceil() as i32).clamp(1, 8);
    let nv = (fv.ceil() as i32).clamp(1, 8);
    let mut sum = [0u32; 3];
    let mut n = 0u32;
    for j in 0..nv {
        let yy = sy - fv * 0.5 + (j as f32 + 0.5) * fv / nv as f32;
        for i in 0..nu {
            let xx = sx - fu * 0.5 + (i as f32 + 0.5) * fu / nu as f32;
            let q = pic_px(p, xx as i32, yy as i32);
            for c in 0..3 {
                sum[c] += q[c] as u32;
            }
            n += 1;
        }
    }
    if n == 0 {
        return [255, 255, 255];
    }
    [(sum[0] / n) as u8, (sum[1] / n) as u8, (sum[2] / n) as u8]
}

// A picture painted in the unit square, through m (the CTM): each page pixel takes what its
// footprint covers in the picture.
fn draw_pic(c: &mut Canvas3, p: &BgPicture, m: &Mat6, clip: RectI) {
    if p.px.is_empty() || p.w < 1 || p.h < 1 || (p.ch != 1 && p.ch != 3) {
        return;
    }
    let Some(inv) = mat_inv(m) else { return };
    let mut x0 = f32::MAX;
    let mut y0 = f32::MAX;
    let mut x1 = f32::MIN;
    let mut y1 = f32::MIN;
    for (u, v) in [(0.0, 0.0), (1.0, 0.0), (1.0, 1.0), (0.0, 1.0)] {
        let (x, y) = mat_pt(m, u, v);
        if !x.is_finite() || !y.is_finite() {
            return;
        }
        x0 = x0.min(x);
        y0 = y0.min(y);
        x1 = x1.max(x);
        y1 = y1.max(y);
    }
    let ix0 = (x0.floor() as i32).max(clip.x0).max(0);
    let iy0 = (y0.floor() as i32).max(clip.y0).max(0);
    let ix1 = (x1.ceil() as i32).min(clip.x1).min(c.w as i32);
    let iy1 = (y1.ceil() as i32).min(clip.y1).min(c.h as i32);
    if ix1 <= ix0 || iy1 <= iy0 {
        return;
    }
    let fu = (inv[0].abs() + inv[2].abs()) * p.w as f32;
    let fv = (inv[1].abs() + inv[3].abs()) * p.h as f32;
    for y in iy0..iy1 {
        for x in ix0..ix1 {
            let (u, v) = mat_pt(&inv, x as f32 + 0.5, y as f32 + 0.5);
            if !(0.0..=1.0).contains(&u) || !(0.0..=1.0).contains(&v) {
                continue;
            }
            let col = pic_sample(p, u * p.w as f32, (1.0 - v) * p.h as f32, fu, fv);
            c.blend(x as usize, y as usize, col, 1.0);
        }
    }
}

// Whether the content stream sets text or draws lines: a page that does is drawn, not read as a
// whole-page picture. (A page that only places images is read as the picture it holds.)
fn content_has_ink(d: &[u8]) -> bool {
    const INK: [&[u8]; 14] = [
        b"BT", b"Tj", b"TJ", b"'", b"\"", b"S", b"s", b"f", b"F", b"f*", b"B", b"B*", b"b", b"b*",
    ];
    let e = d.len();
    let mut p = 0usize;
    while p < e {
        p = skip_ws(d, p, e);
        if p >= e {
            break;
        }
        let q = tok_end(d, p, e);
        if q <= p {
            p += 1;
            continue;
        }
        let t = &d[p..q];
        if INK.contains(&t) {
            return true;
        }
        p = q;
    }
    false
}

// A page's content: its /Contents streams, decoded and joined (a page's content is a stream, or an
// array of them shown one after another).
fn page_content(r: &PdfReader, page: Rng) -> Option<Vec<u8>> {
    let mut c = Rng::default();
    if !dict_get(&r.data, page, "/Contents", &mut c) {
        return None;
    }
    let mut num = 0;
    if ref_num(&r.data, c, &mut num) {
        // (a stream, or an array of streams held by a reference: the reference is followed to the
        // object's own dictionary and stream, which deref would lose)
        let mut dv = Rng::default();
        let mut s = None;
        let mut streamed = false;
        if !obj_parse(r, obj_find(r, num), &mut dv, &mut s, &mut streamed) {
            return None;
        }
        if let Some(s) = s {
            return stream_data(r, dv, s, PDF_MAX_CONTENT);
        }
        c = dv;
    }
    if !deref(r, &mut c) || !is_array(&r.data, c) {
        return None;
    }
    let e = c.e - 1;
    let mut p = c.p + 1;
    let mut item = Rng::default();
    let mut out: Vec<u8> = Vec::new();
    while arr_next(&r.data, &mut p, e, &mut item) {
        let mut num = 0;
        if !ref_num(&r.data, item, &mut num) {
            continue;
        }
        let mut dv = Rng::default();
        let mut s = None;
        let mut streamed = false;
        if !obj_parse(r, obj_find(r, num), &mut dv, &mut s, &mut streamed) {
            continue;
        }
        let Some(s) = s else { continue };
        let Some(part) = stream_data(r, dv, s, PDF_MAX_CONTENT) else { continue };
        if out.len() + part.len() + 1 > PDF_MAX_CONTENT {
            break;
        }
        out.extend_from_slice(&part);
        out.push(b'\n');
    }
    if out.is_empty() { None } else { Some(out) }
}

// A stream's bytes with its filters undone: Flate, ASCIIHex and ASCII85, which is what content,
// forms and font programs carry.
fn stream_data(r: &PdfReader, dv: Rng, s: Stream, cap: usize) -> Option<Vec<u8>> {
    if s.off + s.len > r.data.len() {
        return None;
    }
    let mut data = r.data[s.off..s.off + s.len].to_vec();
    let mut f = [String::new(), String::new(), String::new()];
    let nf = filters_of(r, dv, &mut f);
    for i in 0..nf {
        let out = if is_flate(&f[i]) {
            inflate_grow(&data, cap)?
        } else if f[i] == "ASCIIHexDecode" || f[i] == "AHx" {
            ascii_hex(&data)?
        } else if f[i] == "ASCII85Decode" || f[i] == "A85" {
            ascii85(&data)?
        } else {
            return None;
        };
        if out.len() > cap {
            return None;
        }
        data = out;
    }
    if data.len() > cap { None } else { Some(data) }
}

// stb_image's inflate, the buffer grown until the stream fits (or cap is reached): a content
// stream's size is not known before it is decoded.
fn inflate_grow(src: &[u8], cap: usize) -> Option<Vec<u8>> {
    let mut want = src.len().saturating_mul(16).max(1 << 16).min(cap);
    loop {
        if let Some(v) = inflate_to(src, want) {
            return Some(v);
        }
        if want >= cap {
            return None;
        }
        want = want.saturating_mul(4).min(cap);
    }
}

fn ascii_hex(src: &[u8]) -> Option<Vec<u8>> {
    let mut out = Vec::new();
    let mut hi: i32 = -1;
    for &c in src {
        if c == b'>' {
            break;
        }
        let v = match c {
            b'0'..=b'9' => (c - b'0') as i32,
            b'a'..=b'f' => (c - b'a') as i32 + 10,
            b'A'..=b'F' => (c - b'A') as i32 + 10,
            _ => continue,
        };
        if hi < 0 {
            hi = v;
        } else {
            out.push((hi * 16 + v) as u8);
            hi = -1;
        }
    }
    if hi >= 0 {
        out.push((hi * 16) as u8);
    }
    Some(out)
}

fn ascii85(src: &[u8]) -> Option<Vec<u8>> {
    let s = if src.starts_with(b"<~") { &src[2..] } else { src };
    let mut out: Vec<u8> = Vec::new();
    let mut tuple = [0u32; 5];
    let mut n = 0usize;
    for &c in s {
        if c == b'~' {
            break;
        }
        if is_ws(c) {
            continue;
        }
        if c == b'z' && n == 0 {
            out.extend_from_slice(&[0, 0, 0, 0]);
            continue;
        }
        if !(b'!'..=b'u').contains(&c) {
            return None;
        }
        tuple[n] = (c - b'!') as u32;
        n += 1;
        if n == 5 {
            let mut v: u32 = 0;
            for t in tuple {
                v = v.wrapping_mul(85).wrapping_add(t);
            }
            out.extend_from_slice(&v.to_be_bytes());
            n = 0;
        }
    }
    if n > 1 {
        for k in n..5 {
            tuple[k] = 84;
        }
        let mut v: u32 = 0;
        for t in tuple {
            v = v.wrapping_mul(85).wrapping_add(t);
        }
        out.extend_from_slice(&v.to_be_bytes()[..n - 1]);
    }
    Some(out)
}

// An inline image (BI ... ID <bytes> EI) is passed over: its bytes are not operators, and reading
// them as such would draw nothing but nonsense.
fn skip_inline(d: &[u8], from: usize, e: usize) -> usize {
    let mut q = from;
    let id = loop {
        let at = match find_bytes(d, q, e, b"ID") {
            Some(a) => a,
            None => return e,
        };
        if (at == 0 || is_ws(d[at - 1])) && at + 2 < e && is_ws(d[at + 2]) {
            break at;
        }
        q = at + 1;
    };
    let mut p = (id + 2).min(e);
    if p < e && is_ws(d[p]) {
        p += 1;
    }
    while p + 1 < e {
        if d[p] == b'E' && d[p + 1] == b'I' && is_ws(d[p - 1]) && (p + 2 >= e || is_ws(d[p + 2]) || is_delim(d[p + 2])) {
            return p + 2;
        }
        p += 1;
    }
    e
}

// The page's box (its /CropBox, else its /MediaBox): x0, y0, x1, y1 in points.
fn page_box(r: &PdfReader, page: Rng) -> [f32; 4] {
    let mut v = Rng::default();
    for key in ["/CropBox", "/MediaBox"] {
        let mut a = [0f32; 8];
        if inherited(r, page, key, &mut v) && deref(r, &mut v) && array_nums(&r.data, v, &mut a) >= 4 {
            if a[2] > a[0] && a[3] > a[1] {
                return [a[0], a[1], a[2], a[3]];
            }
        }
    }
    [0.0, 0.0, 612.0, 792.0]
}

// Draws a page into a picture of at most max_w x max_h pixels, as its content stream says.
fn render_page(r: &PdfReader, page: Rng, content: Option<&[u8]>, max_w: i32, max_h: i32, out: &mut BgPicture, why: &mut String) -> i32 {
    let b = page_box(r, page);
    let pw = b[2] - b[0];
    let ph = b[3] - b[1];
    if !(pw > 0.0 && ph > 0.0) || !pw.is_finite() || !ph.is_finite() {
        why_set(why, "the page has no size");
        return PDF_ERR_FORMAT;
    }
    let mw = max_w.max(1) as f32;
    let mh = max_h.max(1) as f32;
    let s = (mw / pw).min(mh / ph);
    if !(s > 0.0) || !s.is_finite() {
        why_set(why, "the page has no size");
        return PDF_ERR_FORMAT;
    }
    let cw = ((pw * s).round() as i32).clamp(1, 8192);
    let ch = ((ph * s).round() as i32).clamp(1, 8192);
    let Some(canvas) = Canvas3::white(cw as usize, ch as usize) else {
        why_set(why, "out of memory");
        return PDF_ERR_MEM;
    };
    // Page points to canvas pixels: x to the right, y down (a PDF's y goes up).
    let base: Mat6 = [s, 0.0, 0.0, -s, -b[0] * s, ch as f32 + b[1] * s];
    let mut res = Rng::default();
    if !inherited(r, page, "/Resources", &mut res) || !deref(r, &mut res) {
        res = Rng::default();
    }
    let mut cx = PgCtx::new(r, canvas, base, res);
    if let Some(c) = content {
        cx.run(c);
    }
    *out = BgPicture { px: cx.canvas.px, w: cw, h: ch, ch: 3 };
    PDF_OK
}
