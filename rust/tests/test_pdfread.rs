// test_pdfread.rs: the page pictures of a PDF (src/pdfread.h): the picture a page holds, its
// predictors, its turning, and the pages Grimoire will not show (text set in fonts, masks, JPEG
// 2000), on hand-made PDFs in a scratch folder. The port of tests/test_pdfread.c: the same tests,
// in the C's order, with the same checks.
#![allow(clippy::needless_range_loop)] // (the C's index loops, kept)
mod testlib;
use grimoire::ffi_stb;
use grimoire::prelude::*;
use std::sync::OnceLock;
use testlib::*;

static DIR: OnceLock<String> = OnceLock::new();

fn dir() -> &'static str {
    DIR.get().map(String::as_str).unwrap_or("")
}

fn put_pdf(name: &str, buf: &[u8]) -> String {
    let path = format!("{}/{name}", dir());
    check!(std::fs::write(&path, buf).is_ok());
    path
}

// One page holding one image: the image's stream already compressed, the page's colour space and
// bits a sample, and any other keys of the page's dictionary ("/Rotate 90").
fn make_pdf(w: i32, h: i32, img: &[u8], cs: &str, bpc: i32, extra: &str) -> Vec<u8> {
    let mut out = String::new();
    out.push_str("%PDF-1.4\n");
    out.push_str("1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n");
    out.push_str("2 0 obj\n<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n");
    out.push_str(&cformat!(
        "3 0 obj\n<< /Type /Page /Parent 2 0 R /Resources << /XObject << /Im0 4 0 R >> >> %s >>\nendobj\n",
        extra
    ));
    out.push_str(&cformat!(
        "4 0 obj\n<< /Type /XObject /Subtype /Image /Width %d /Height %d /ColorSpace %s \
/BitsPerComponent %d /Filter /FlateDecode /Length %d >>\nstream\n",
        w,
        h,
        cs,
        bpc,
        img.len() as i32
    ));
    let mut bytes = out.into_bytes();
    bytes.extend_from_slice(img);
    bytes.extend_from_slice(b"\nendstream\nendobj\ntrailer\n<< /Root 1 0 R >>\n%%EOF\n");
    bytes
}

// A page whose content is the given operators, with no image at all: what a book exported from
// another app holds. With font, the page's /F1 is a TrueType font whose program is the Terminess
// face the app ships (a real embedded font, as a PDF of text carries).
fn make_page_pdf(content: &str, media: &str, font: bool) -> Vec<u8> {
    let mut out = String::new();
    out.push_str("%PDF-1.4\n");
    out.push_str("1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n");
    out.push_str("2 0 obj\n<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n");
    out.push_str(&format!("3 0 obj\n<< /Type /Page /Parent 2 0 R /MediaBox {media} "));
    if font {
        out.push_str("/Resources << /Font << /F1 5 0 R >> >> ");
    }
    out.push_str("/Contents 4 0 R >>\nendobj\n");
    out.push_str(&format!(
        "4 0 obj\n<< /Length {} >>\nstream\n{content}\nendstream\nendobj\n",
        content.len()
    ));
    let mut bytes = out.into_bytes();
    if font {
        let ttf = grimoire::assets::FONT_TERMINESS_REGULAR;
        let mut widths = String::new();
        for _ in 32..=126 {
            widths.push_str("600 ");
        }
        bytes.extend_from_slice(
            format!(
                "5 0 obj\n<< /Type /Font /Subtype /TrueType /BaseFont /Terminess /FirstChar 32 \
/LastChar 126 /Widths [{widths}] /Encoding /WinAnsiEncoding /FontDescriptor 6 0 R >>\nendobj\n"
            )
            .as_bytes(),
        );
        bytes.extend_from_slice(
            b"6 0 obj\n<< /Type /FontDescriptor /FontName /Terminess /Flags 32 /FontBBox [0 -200 1000 800] \
/ItalicAngle 0 /Ascent 800 /Descent -200 /CapHeight 700 /StemV 80 /FontFile2 7 0 R >>\nendobj\n",
        );
        let mut s = format!(
            "7 0 obj\n<< /Length {} /Length1 {} >>\nstream\n",
            ttf.len(),
            ttf.len()
        )
        .into_bytes();
        s.extend_from_slice(ttf);
        s.extend_from_slice(b"\nendstream\nendobj\n");
        bytes.extend_from_slice(&s);
    }
    bytes.extend_from_slice(b"trailer\n<< /Root 1 0 R >>\n%%EOF\n");
    bytes
}

fn dark_pixels(p: &BgPicture) -> i32 {
    let ch = p.ch as usize;
    let mut n = 0;
    for i in 0..p.w as usize * p.h as usize {
        if p.px[i * ch] < 128 {
            n += 1;
        }
    }
    n
}

// The rightmost column with ink in it (-1 for none).
fn right_ink(p: &BgPicture) -> i32 {
    let ch = p.ch as usize;
    let mut right = -1;
    for y in 0..p.h as usize {
        for x in 0..p.w as usize {
            if p.px[(y * p.w as usize + x) * ch] < 128 {
                right = right.max(x as i32);
            }
        }
    }
    right
}

// A PDF 1.5 whose catalog, page tree and page are inside a compressed object stream (as modern
// files keep them), with one page drawn by a vector fill.
fn make_objstm_pdf() -> Vec<u8> {
    let objects: [(i32, &str); 3] = [
        (2, "<< /Type /Catalog /Pages 3 0 R >>"),
        (3, "<< /Type /Pages /Kids [4 0 R] /Count 1 >>"),
        (4, "<< /Type /Page /Parent 3 0 R /MediaBox [0 0 100 100] /Contents 5 0 R >>"),
    ];
    let mut pairs = String::new();
    let mut bodies = String::new();
    for (num, body) in objects {
        pairs.push_str(&format!("{num} {} ", bodies.len()));
        bodies.push_str(body);
        bodies.push(' ');
    }
    let first = pairs.len();
    let stream = format!("{pairs}{bodies}");
    let z = deflate(stream.as_bytes());
    let content = "0 0 1 rg 0 0 100 100 re f";
    let mut out = String::new();
    out.push_str("%PDF-1.5\n");
    out.push_str(&format!(
        "1 0 obj\n<< /Type /ObjStm /N 3 /First {first} /Filter /FlateDecode /Length {} >>\nstream\n",
        z.len()
    ));
    let mut bytes = out.into_bytes();
    bytes.extend_from_slice(&z);
    bytes.extend_from_slice(b"\nendstream\nendobj\n");
    bytes.extend_from_slice(
        format!(
            "5 0 obj\n<< /Length {} >>\nstream\n{content}\nendstream\nendobj\n",
            content.len()
        )
        .as_bytes(),
    );
    bytes.extend_from_slice(b"trailer\n<< /Root 2 0 R >>\n%%EOF\n");
    bytes
}

// stb_image_write's deflate (stb_impl.c), for the Flate streams a PDF holds.
fn deflate(raw: &[u8]) -> Vec<u8> {
    let mut zl: i32 = 0;
    // SAFETY: stbi_zlib_compress reads raw.len() bytes from raw and returns a malloc block whose
    // length it stores in zl.
    let z = unsafe { ffi_stb::stbi_zlib_compress(raw.as_ptr() as *mut u8, raw.len() as i32, &mut zl, 0) };
    check!(!z.is_null() && zl > 0);
    if z.is_null() {
        return Vec::new();
    }
    // SAFETY: the call returned zl bytes in a block of its own.
    let out = unsafe { std::slice::from_raw_parts(z, zl as usize) }.to_vec();
    // SAFETY: the block came from malloc inside stb_image_write, and is not read again.
    unsafe { libc::free(z as *mut libc::c_void) };
    out
}

fn not_a_pdf() {
    let path = put_pdf("notes.txt", b"hello");
    let mut r: Option<Box<PdfReader>> = None;
    let mut np = 0;
    let mut why = String::new();
    check!(pdf_open(&path, &mut r, &mut np, &mut why) == PDF_ERR_FORMAT);
    check!(r.is_none() && np == 0 && !why.is_empty());
}

fn gray_page() {
    let mut raw = [0u8; 16];
    for i in 0..16 {
        raw[i] = (i * 16) as u8;
    }
    let z = deflate(&raw);
    let pdf = make_pdf(4, 4, &z, "/DeviceGray", 8, "");
    let path = put_pdf("gray.pdf", &pdf);
    let mut r: Option<Box<PdfReader>> = None;
    let mut np = 0;
    let mut why = String::new();
    check!(pdf_open(&path, &mut r, &mut np, &mut why) == PDF_OK);
    check!(np == 1);
    let mut p = BgPicture::default();
    let reader = r.as_deref().unwrap();
    check!(pdf_page_picture(reader, 0, 1000, 1000, &mut p, &mut why) == PDF_OK);
    check!(p.w == 4 && p.h == 4 && p.ch == 1);
    for i in 0..16 {
        check!(p.px[i] == (i * 16) as u8);
    }
    bgpicture_free(&mut p);
    pdf_close(&mut r);
}

fn bilevel_page() {
    // 8 x 2, a byte a row: four black then four white, then the other way round.
    let raw = [0x0Fu8, 0xF0];
    let z = deflate(&raw);
    let pdf = make_pdf(8, 2, &z, "/DeviceGray", 1, "");
    let path = put_pdf("bilevel.pdf", &pdf);
    let mut r: Option<Box<PdfReader>> = None;
    let mut np = 0;
    let mut why = String::new();
    check!(pdf_open(&path, &mut r, &mut np, &mut why) == PDF_OK);
    let mut p = BgPicture::default();
    let reader = r.as_deref().unwrap();
    check!(pdf_page_picture(reader, 0, 1000, 1000, &mut p, &mut why) == PDF_OK);
    check!(p.w == 8 && p.h == 2 && p.ch == 1);
    check!(p.px[0] == 0 && p.px[3] == 0 && p.px[4] == 255 && p.px[7] == 255);
    check!(p.px[8] == 255 && p.px[11] == 255 && p.px[12] == 0 && p.px[15] == 0);
    bgpicture_free(&mut p);
    pdf_close(&mut r);
}

fn down_to_a_page_size() {
    let raw = [128u8; 400 * 400];
    let z = deflate(&raw);
    let pdf = make_pdf(400, 400, &z, "/DeviceGray", 8, "");
    let path = put_pdf("big.pdf", &pdf);
    let mut r: Option<Box<PdfReader>> = None;
    let mut np = 0;
    let mut why = String::new();
    check!(pdf_open(&path, &mut r, &mut np, &mut why) == PDF_OK);
    let mut p = BgPicture::default();
    let reader = r.as_deref().unwrap();
    check!(pdf_page_picture(reader, 0, 100, 100, &mut p, &mut why) == PDF_OK);
    check!(p.w == 100 && p.h == 100);
    check!(p.px[0] == 128 && p.px[100 * 99 + 99] == 128);
    bgpicture_free(&mut p);
    pdf_close(&mut r);
}

fn a_page_turned_a_quarter_turn() {
    let raw = [0u8, 200];
    let z = deflate(&raw);
    let pdf = make_pdf(2, 1, &z, "/DeviceGray", 8, "/Rotate 90");
    let path = put_pdf("turned.pdf", &pdf);
    let mut r: Option<Box<PdfReader>> = None;
    let mut np = 0;
    let mut why = String::new();
    check!(pdf_open(&path, &mut r, &mut np, &mut why) == PDF_OK);
    let mut p = BgPicture::default();
    let reader = r.as_deref().unwrap();
    check!(pdf_page_picture(reader, 0, 1000, 1000, &mut p, &mut why) == PDF_OK);
    check!(p.w == 1 && p.h == 2 && p.ch == 1);
    check!(p.px[0] == 0 && p.px[1] == 200);
    bgpicture_free(&mut p);
    pdf_close(&mut r);
}

// A page set in fonts is drawn, not refused: the text arrives as ink on white paper.
fn text_page_is_drawn() {
    let content = "0 g BT /F1 40 Tf 10 30 Td (Hello) Tj ET";
    let pdf = make_page_pdf(content, "[0 0 200 100]", true);
    let path = put_pdf("text.pdf", &pdf);
    let mut r: Option<Box<PdfReader>> = None;
    let mut np = 0;
    let mut why = String::new();
    check!(pdf_open(&path, &mut r, &mut np, &mut why) == PDF_OK);
    check!(np == 1);
    let mut p = BgPicture::default();
    let reader = r.as_deref().unwrap();
    check!(pdf_page_picture(reader, 0, 1000, 1000, &mut p, &mut why) == PDF_OK);
    check!(p.w == 1000 && p.h == 500 && p.ch == 3);
    check!(dark_pixels(&p) > 200);
    check!(p.px[0] == 255 && p.px[1] == 255 && p.px[2] == 255); // (the corner is paper)
    bgpicture_free(&mut p);
    pdf_close(&mut r);
}

// A font the page names but does not carry still draws (Grimoire's own face, the PDF's advances).
fn text_page_without_a_font_is_drawn() {
    let content = "0 g BT /F1 40 Tf 10 30 Td (Hello) Tj ET";
    let pdf = make_page_pdf(content, "[0 0 200 100]", false);
    let path = put_pdf("nofont.pdf", &pdf);
    let mut r: Option<Box<PdfReader>> = None;
    let mut np = 0;
    let mut why = String::new();
    check!(pdf_open(&path, &mut r, &mut np, &mut why) == PDF_OK);
    let mut p = BgPicture::default();
    let reader = r.as_deref().unwrap();
    check!(pdf_page_picture(reader, 0, 1000, 1000, &mut p, &mut why) == PDF_OK);
    check!(dark_pixels(&p) > 200);
    // The face is drawn as wide as the PDF's advances (500 here), so the run ends where they say
    // instead of running past its last glyph: the page is 200 pt across, drawn 5 px to the point,
    // the text starts 10 pt in and each of the five glyphs advances 20 pt.
    let end = 10 * 5 + 5 * (500 * 40 * 5 / 1000) + 6;
    check!(right_ink(&p) <= end);
    bgpicture_free(&mut p);
    pdf_close(&mut r);
}

// A file whose objects are all in a compressed object stream is read like any other.
fn objects_in_a_compressed_stream() {
    let pdf = make_objstm_pdf();
    let path = put_pdf("objstm.pdf", &pdf);
    let mut r: Option<Box<PdfReader>> = None;
    let mut np = 0;
    let mut why = String::new();
    check!(pdf_open(&path, &mut r, &mut np, &mut why) == PDF_OK);
    check!(np == 1);
    let mut p = BgPicture::default();
    let reader = r.as_deref().unwrap();
    check!(pdf_page_picture(reader, 0, 100, 100, &mut p, &mut why) == PDF_OK);
    check!(p.px[0] == 0 && p.px[2] == 255);
    bgpicture_free(&mut p);
    pdf_close(&mut r);
}

// Lines and fills: a filled square covers the page in its colour.
fn vector_page_is_drawn() {
    let pdf = make_page_pdf("0 0 1 rg 0 0 100 100 re f", "[0 0 100 100]", false);
    let path = put_pdf("vector.pdf", &pdf);
    let mut r: Option<Box<PdfReader>> = None;
    let mut np = 0;
    let mut why = String::new();
    check!(pdf_open(&path, &mut r, &mut np, &mut why) == PDF_OK);
    let mut p = BgPicture::default();
    let reader = r.as_deref().unwrap();
    check!(pdf_page_picture(reader, 0, 100, 100, &mut p, &mut why) == PDF_OK);
    check!(p.w == 100 && p.h == 100 && p.ch == 3);
    check!(p.px[0] == 0 && p.px[1] == 0 && p.px[2] == 255);
    check!(p.px[3 * (100 * 50 + 50)] == 0 && p.px[3 * (100 * 50 + 50) + 2] == 255);
    bgpicture_free(&mut p);
    pdf_close(&mut r);
}

fn a_missing_file() {
    let mut r: Option<Box<PdfReader>> = None;
    let mut np = 0;
    let mut why = String::new();
    check!(pdf_open("/nonexistent/none.pdf", &mut r, &mut np, &mut why) == PDF_ERR_READ);
    check!(r.is_none() && np == 0);
}

#[test]
fn test_pdfread() {
    let d = format!("{}/pdfread-{}", tl_tmp(), std::process::id());
    let _ = std::fs::remove_dir_all(&d);
    check!(std::fs::create_dir_all(&d).is_ok());
    let _ = DIR.set(d.clone());
    run!(not_a_pdf);
    run!(gray_page);
    run!(bilevel_page);
    run!(down_to_a_page_size);
    run!(a_page_turned_a_quarter_turn);
    run!(text_page_is_drawn);
    run!(text_page_without_a_font_is_drawn);
    run!(vector_page_is_drawn);
    run!(objects_in_a_compressed_stream);
    run!(a_missing_file);
    done();
    let _ = std::fs::remove_dir_all(&d);
}
