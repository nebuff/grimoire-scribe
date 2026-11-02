// pdfread.c: page pictures out of a PDF (pdfread.h). See docs/EXPORT.md.
//
// No fonts, no vector graphics, no transparency groups: a page is read as the whole-page picture it
// holds, which every scan, every photographed page and most PDFs exported from other apps carry.
// The objects are found by scanning the file for "N G obj" rather than by its cross-reference table
// (a table this reader would have to trust, and that many files get slightly wrong): a later
// definition of an object is the one that counts, as an incremental update means it to be.
//
// Everything here runs in the import's forked child. Every read is bounds-checked against the file
// and every allocation against what a page may take (PDF_MAX_*): a PDF is untrusted input.
#include "pdfread.h"

#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// stb_image's inflate, compiled into the core by bgimage.c (third_party/stb_image.h). It decodes
// into the buffer given and never past it: the bound is ours, not the file's.
int stbi_zlib_decode_buffer(char *obuffer, int olen, const char *ibuffer, int ilen);

#define PDF_MAX_BYTES ((size_t)96 << 20)    // the biggest PDF read at all
#define PDF_MAX_PIXELS BG_MAX_PIXELS        // and the biggest page picture it may hold
#define PDF_MAX_SAMPLES ((size_t)160 << 20) // the most a page's samples (or a decoded JPEG) may take
#define PDF_MAX_PAGES 2000                  // as many pages as a notebook holds
#define PDF_MAX_OBJ 400000                  // objects in the file
#define PDF_MAX_DEPTH 32                    // the page tree, and a form's resources, this deep

struct PdfReader {
    uint8_t *data;
    size_t len;
    struct {
        int num;
        size_t off;  // just past its "obj": where its value begins
    } *obj;
    int nobj, cap;
    int *pages;
    int npages, pcap;
};

typedef struct {
    const uint8_t *p, *e;
} Rng;  // a slice of the file

static void why_set(char *why, const char *fmt, ...) {
    if (!why) return;
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(why, PDF_WHY_LEN, fmt, ap);
    va_end(ap);
}

// ---- tokens ----

static bool is_ws(uint8_t c) { return c == 0 || c == 9 || c == 10 || c == 12 || c == 13 || c == 32; }
static bool is_digit(uint8_t c) { return c >= '0' && c <= '9'; }

static bool is_delim(uint8_t c) {
    switch (c) {
    case '(':
    case ')':
    case '<':
    case '>':
    case '[':
    case ']':
    case '{':
    case '}':
    case '/':
    case '%': return true;
    default: return false;
    }
}

static const uint8_t *skip_ws(const uint8_t *p, const uint8_t *e) {
    while (p < e) {
        if (is_ws(*p)) {
            p++;
        } else if (*p == '%') {
            while (p < e && *p != '\n' && *p != '\r') p++;
        } else {
            break;
        }
    }
    return p;
}

// Past a literal string at p (on its '('), its escapes and nested parentheses included.
static const uint8_t *skip_string(const uint8_t *p, const uint8_t *e) {
    int depth = 0;
    for (; p < e; p++) {
        if (*p == '\\') {
            p++;
            continue;
        }
        if (*p == '(') {
            depth++;
        } else if (*p == ')' && --depth == 0) {
            return p + 1;
        }
    }
    return e;
}

static const uint8_t *array_end(const uint8_t *p, const uint8_t *e);

// Past one value at p: a dictionary, an array, a string, a name, or a number or keyword.
static const uint8_t *tok_end(const uint8_t *p, const uint8_t *e) {
    if (p >= e) return p;
    if (*p == '<' && p + 1 < e && p[1] == '<') {  // a dictionary
        int depth = 0;
        while (p < e) {
            if (*p == '<' && p + 1 < e && p[1] == '<') {
                depth++;
                p += 2;
            } else if (*p == '>' && p + 1 < e && p[1] == '>') {
                p += 2;
                if (--depth == 0) return p;
            } else if (*p == '(') {
                p = skip_string(p, e);
            } else if (*p == '[') {
                p = array_end(p, e);
            } else if (*p == '<') {  // a hex string
                while (p < e && *p++ != '>') {}
            } else if (*p == '%') {
                while (p < e && *p != '\n' && *p != '\r') p++;
            } else if (*p == '/') {
                p++;
                while (p < e && !is_ws(*p) && !is_delim(*p)) p++;
            } else {
                p++;
            }
        }
        return e;
    }
    if (*p == '[') return array_end(p, e);
    if (*p == '(') return skip_string(p, e);
    if (*p == '<') {
        p++;
        while (p < e && *p != '>') p++;
        return p < e ? p + 1 : e;
    }
    if (*p == '/') {
        p++;
        while (p < e && !is_ws(*p) && !is_delim(*p)) p++;
        return p;
    }
    while (p < e && !is_ws(*p) && !is_delim(*p)) p++;
    return p;
}

static const uint8_t *array_end(const uint8_t *p, const uint8_t *e) {
    int depth = 0;
    while (p < e) {
        if (*p == '[') {
            depth++;
            p++;
        } else if (*p == ']') {
            p++;
            if (--depth == 0) return p;
        } else if (*p == '(') {
            p = skip_string(p, e);
        } else if (*p == '<' && p + 1 < e && p[1] == '<') {
            p = tok_end(p, e);
        } else if (*p == '<') {
            while (p < e && *p++ != '>') {}
        } else if (*p == '%') {
            while (p < e && *p != '\n' && *p != '\r') p++;
        } else {
            p++;
        }
    }
    return e;
}

// Past the value at p, its reference's other two tokens included ("12 0 R").
static const uint8_t *value_end(const uint8_t *p, const uint8_t *e) {
    const uint8_t *a = tok_end(p, e);
    const uint8_t *b = skip_ws(a, e);
    if (b > a && b < e && (is_digit(*b) || *b == '-' || *b == '+')) {  // ("12 0 R")
        const uint8_t *c = tok_end(b, e);
        const uint8_t *d = skip_ws(c, e);
        if (d < e && (*d == 'R' || *d == 'r') && (d + 1 >= e || is_ws(d[1]) || is_delim(d[1]))) return d + 1;
    }
    return a;
}

static bool span_is(const Rng *v, const char *s) {
    size_t n = strlen(s);
    return v->p && (size_t)(v->e - v->p) == n && !memcmp(v->p, s, n);
}

// The number in a span, if it is one (a copy of it at most 31 bytes, so no read runs past it).
static bool span_long(const Rng *v, long *out) {
    char buf[32];
    size_t n = (size_t)(v->e - v->p);
    if (!v->p || n == 0 || n >= sizeof buf) return false;
    memcpy(buf, v->p, n);
    buf[n] = 0;
    char *end;
    long v2 = strtol(buf, &end, 10);
    if (end == buf) return false;
    *out = v2;
    return true;
}

// Whether the value is an indirect reference ("12 0 R"), and its object number.
static bool ref_num(const Rng *v, int *num) {
    char buf[40];
    size_t n = (size_t)(v->e - v->p);
    if (!v->p || n == 0 || n >= sizeof buf) return false;
    memcpy(buf, v->p, n);
    buf[n] = 0;
    long a, b;
    char r;
    if (sscanf(buf, "%ld %ld %c", &a, &b, &r) != 3 || r != 'R' || a <= 0 || a > 1000000) return false;
    *num = (int)a;
    return true;
}

// ---- objects ----

static const uint8_t *find_bytes(const uint8_t *p, const uint8_t *e, const char *needle) {
    size_t n = strlen(needle);
    if (!n || (size_t)(e - p) < n) return NULL;
    for (const uint8_t *q = p; q + n <= e; q++)
        if (*q == (uint8_t)needle[0] && !memcmp(q, needle, n)) return q;
    return NULL;
}

static size_t obj_find(const PdfReader *r, int num) {
    int lo = 0, hi = r->nobj - 1;
    while (lo <= hi) {
        int mid = lo + (hi - lo) / 2;
        if (r->obj[mid].num == num) return r->obj[mid].off;
        if (r->obj[mid].num < num) lo = mid + 1;
        else hi = mid - 1;
    }
    return 0;
}

static bool value_starts(const uint8_t *p, const uint8_t *e) {
    p = skip_ws(p, e);
    if (p >= e) return false;
    return *p == '<' || *p == '[' || *p == '(' || *p == '/' || is_digit(*p) || *p == '-' || *p == '+' ||
           *p == '.' || *p == 't' || *p == 'f' || *p == 'n';
}

// The object at off ("N G obj" scanned): its value, and the bytes of its stream when it has one.
static bool obj_parse(const PdfReader *r, size_t off, Rng *val, const uint8_t **stream, size_t *slen,
                      bool *streamed) {
    const uint8_t *d = r->data, *e = d + r->len;
    if (off == 0 || off >= r->len) return false;
    const uint8_t *p = skip_ws(d + off, e);
    if (!value_starts(p, e)) return false;
    const uint8_t *ve = value_end(p, e);
    *val = (Rng){p, ve};
    if (stream) *stream = NULL;
    if (slen) *slen = 0;
    if (streamed) *streamed = false;
    if (p[0] != '<' || p + 1 >= ve || p[1] != '<') return true;
    const uint8_t *q = skip_ws(ve, e);
    if ((size_t)(e - q) < 6 || memcmp(q, "stream", 6)) return true;
    if (streamed) *streamed = true;
    q += 6;
    if (q < e && *q == '\r') q++;
    if (q < e && *q == '\n') q++;
    if (!stream || !slen) return true;
    // Its /Length, when the file gives one that fits (some writers get it wrong: then its endstream
    // says where it ends).
    size_t len = 0;
    bool have = false;
    const uint8_t *kp = val->p + 2, *ke = val->e - 2;
    Rng key, lv;
    while (kp < ke) {
        key.p = skip_ws(kp, ke);
        if (key.p >= ke || *key.p != '/') break;
        key.e = tok_end(key.p, ke);
        const uint8_t *v = skip_ws(key.e, ke);
        if (v >= ke) break;
        lv = (Rng){v, value_end(v, ke)};
        if (span_is(&key, "/Length")) {
            long l = 0;
            if (span_long(&lv, &l)) {
                have = l > 0;
                len = have ? (size_t)l : 0;
            } else {  // an indirect length
                int num;
                if (ref_num(&lv, &num)) {
                    Rng nv;
                    if (obj_parse(r, obj_find(r, num), &nv, NULL, NULL, NULL) && span_long(&nv, &l) && l > 0) {
                        have = true;
                        len = (size_t)l;
                    }
                }
            }
            break;
        }
        kp = skip_ws(lv.e, ke);
    }
    if (have && (size_t)(e - q) >= len && len <= PDF_MAX_BYTES) {
        const uint8_t *after = skip_ws(q + len, e);
        if ((size_t)(e - after) >= 9 && !memcmp(after, "endstream", 9)) {
            *stream = q;
            *slen = len;
            return true;
        }
    }
    const uint8_t *es = find_bytes(q, e, "endstream");
    if (!es) return false;
    size_t flen = (size_t)(es - q);
    while (flen && (q[flen - 1] == '\n' || q[flen - 1] == '\r')) flen--;
    *stream = q;
    *slen = flen;
    return true;
}

static bool obj_value(const PdfReader *r, int num, Rng *val) {
    return obj_parse(r, obj_find(r, num), val, NULL, NULL, NULL);
}

// The value, with any indirect reference followed to what it names.
static bool deref(const PdfReader *r, Rng *v, int depth) {
    for (int i = 0; i < 8; i++) {
        int num;
        if (!ref_num(v, &num)) return true;
        if (num == 0) {
            *v = (Rng){NULL, NULL};
            return true;
        }
        Rng nv;
        if (!obj_value(r, num, &nv)) return false;
        *v = nv;
        (void)depth;
    }
    return false;
}

static bool is_dict(const Rng *v) { return v->p && v->e - v->p >= 4 && v->p[0] == '<' && v->p[1] == '<'; }
static bool is_array(const Rng *v) { return v->p && v->e > v->p && v->p[0] == '['; }

// The value of key ("/Type") in dictionary d, as it is (a reference not followed).
static bool dict_get(const Rng *d, const char *key, Rng *val) {
    if (!is_dict(d)) return false;
    const uint8_t *p = skip_ws(d->p + 2, d->e - 2), *e = d->e - 2;
    while (p < e) {
        const uint8_t *k = tok_end(p, e);
        if (*p == '/' && span_is(&(Rng){p, k}, key)) {
            const uint8_t *v = skip_ws(k, e);
            if (v >= e) return false;
            *val = (Rng){v, value_end(v, e)};
            return true;
        }
        p = skip_ws(k, e);
    }
    return false;
}

// The next name and value of a dictionary (p from d.p + 2, e d.e - 2).
static bool dict_next(const uint8_t **p, const uint8_t *e, Rng *key, Rng *val) {
    const uint8_t *q = skip_ws(*p, e);
    if (q >= e || *q != '/') return false;
    key->p = q;
    key->e = tok_end(q, e);
    const uint8_t *v = skip_ws(key->e, e);
    if (v >= e) return false;
    val->p = v;
    val->e = value_end(v, e);
    *p = skip_ws(val->e, e);
    return true;
}

static bool arr_next(const uint8_t **p, const uint8_t *e, Rng *item) {
    const uint8_t *q = skip_ws(*p, e);
    if (q >= e || *q == ']') return false;
    item->p = q;
    item->e = value_end(q, e);
    *p = skip_ws(item->e, e);
    return true;
}

// A name's text without its '/', copied ("" when the value is not a name).
static void span_name(const Rng *v, char *out, size_t cap) {
    size_t n = 0;
    out[0] = 0;
    if (!v->p || *v->p != '/') return;
    for (const uint8_t *q = v->p + 1; q < v->e && n + 1 < cap; q++) out[n++] = (char)*q;
    out[n] = 0;
}

// The name key of dictionary d, followed through references.
static bool dict_name(const PdfReader *r, const Rng *d, const char *key, char *out, size_t cap) {
    Rng v;
    out[0] = 0;
    if (!dict_get(d, key, &v) || !deref(r, &v, 0)) return false;
    span_name(&v, out, cap);
    return out[0] != 0;
}

static bool dict_long(const PdfReader *r, const Rng *d, const char *key, long *out) {
    Rng v;
    if (!dict_get(d, key, &v) || !deref(r, &v, 0)) return false;
    return span_long(&v, out);
}

// A dictionary object by its number: for a page or a page tree's node.
static bool obj_dict(const PdfReader *r, int num, Rng *d) {
    Rng v;
    if (!obj_value(r, num, &v) || !deref(r, &v, 0) || !is_dict(&v)) return false;
    *d = v;
    return true;
}

// ---- the file's objects, and its page tree ----

static void obj_add(PdfReader *r, int num, size_t off) {
    if (r->nobj == r->cap) {
        int nc = r->cap ? r->cap * 2 : 512;
        if (nc > PDF_MAX_OBJ) nc = PDF_MAX_OBJ;
        if (r->nobj >= nc) return;
        void *nv = realloc(r->obj, (size_t)nc * sizeof *r->obj);
        if (!nv) return;
        r->obj = nv;
        r->cap = nc;
    }
    r->obj[r->nobj].num = num;
    r->obj[r->nobj].off = off;
    r->nobj++;
}

static int cmp_obj(const void *a, const void *b) {
    const int pn = ((const int *)a)[0], qn = ((const int *)b)[0];
    if (pn != qn) return pn < qn ? -1 : 1;
    const size_t po = ((const size_t *)((const char *)a + sizeof(int)))[0];
    const size_t qo = ((const size_t *)((const char *)b + sizeof(int)))[0];
    return po < qo ? -1 : po > qo;
}

// Every "N G obj" in the file. One whose value does not start the way a value does is a coincidence
// in a stream, not an object; of two with the same number, the later holds it (an update).
static void scan_objects(PdfReader *r) {
    const uint8_t *d = r->data, *e = d + r->len;
    for (size_t i = 0; i + 3 < r->len; i++) {
        if (d[i] != 'o' || d[i + 1] != 'b' || d[i + 2] != 'j') continue;
        if (i + 3 < r->len && !is_ws(d[i + 3]) && !is_delim(d[i + 3])) continue;
        size_t j = i;
        while (j > 0 && is_ws(d[j - 1])) j--;
        size_t gen_end = j;
        while (j > 0 && is_digit(d[j - 1])) j--;
        if (j == gen_end) continue;
        if (j == 0 || !is_ws(d[j - 1])) continue;
        while (j > 0 && is_ws(d[j - 1])) j--;
        size_t num_end = j;
        while (j > 0 && is_digit(d[j - 1])) j--;
        if (j == num_end) continue;
        if (j > 0 && !is_ws(d[j - 1]) && !is_delim(d[j - 1])) continue;
        size_t num_len = num_end - j;
        if (num_len == 0 || num_len > 9) continue;
        long num = 0;
        for (size_t k = j; k < num_end; k++) num = num * 10 + (d[k] - '0');
        if (num <= 0 || num > 1000000) continue;
        size_t off = i + 3;
        if (!value_starts(d + off, e)) continue;
        obj_add(r, (int)num, off);
        i += 2;
    }
    if (r->nobj > 1) qsort(r->obj, (size_t)r->nobj, sizeof *r->obj, cmp_obj);
    // One entry a number: the last of its run (its latest definition).
    int kept = 0;
    for (int i = 0; i < r->nobj; i++) {
        if (i + 1 < r->nobj && r->obj[i + 1].num == r->obj[i].num) continue;
        r->obj[kept++] = r->obj[i];
    }
    r->nobj = kept;
}

static void page_add(PdfReader *r, int num) {
    if (r->npages >= PDF_MAX_PAGES) return;
    if (r->npages == r->pcap) {
        int nc = r->pcap ? r->pcap * 2 : 64;
        if (nc > PDF_MAX_PAGES) nc = PDF_MAX_PAGES;
        void *nv = realloc(r->pages, (size_t)nc * sizeof *r->pages);
        if (!nv) return;
        r->pages = nv;
        r->pcap = nc;
    }
    r->pages[r->npages++] = num;
}

// A value a page takes from its parent Pages node when it does not give one itself.
static bool inherited(const PdfReader *r, Rng page, const char *key, Rng *out) {
    Rng d = page;
    for (int depth = 0; depth < 8; depth++) {
        if (dict_get(&d, key, out)) return true;
        Rng parent;
        if (!dict_get(&d, "/Parent", &parent) || !deref(r, &parent, 0) || !is_dict(&parent)) return false;
        d = parent;
    }
    return false;
}

static void walk_pages(PdfReader *r, int num, int depth) {
    if (depth > PDF_MAX_DEPTH || r->npages >= PDF_MAX_PAGES) return;
    Rng d;
    if (!obj_dict(r, num, &d)) return;
    char type[24];
    dict_name(r, &d, "/Type", type, sizeof type);
    Rng kids;
    bool pages = !strcmp(type, "Pages") || (!strcmp(type, "Page") ? false : dict_get(&d, "/Kids", &kids));
    if (pages) {
        if (!dict_get(&d, "/Kids", &kids) || !deref(r, &kids, 0) || !is_array(&kids)) return;
        const uint8_t *p = kids.p + 1, *e = kids.e - 1;
        Rng kid;
        while (arr_next(&p, e, &kid)) {
            int k;
            if (!ref_num(&kid, &k)) continue;
            walk_pages(r, k, depth + 1);
            if (r->npages >= PDF_MAX_PAGES) return;
        }
        return;
    }
    page_add(r, num);
}

static bool find_catalog(PdfReader *r, Rng *catalog) {
    for (int i = 0; i < r->nobj; i++) {
        Rng d;
        if (!obj_dict(r, r->obj[i].num, &d)) continue;
        char type[24];
        if (dict_name(r, &d, "/Type", type, sizeof type) && !strcmp(type, "Catalog")) {
            *catalog = d;
            return true;
        }
    }
    return false;
}

int pdf_open(const char *path, PdfReader **out, int *npages, char *why) {
    *out = NULL;
    *npages = 0;
    why_set(why, "the file does not read");
    size_t len;
    uint8_t *data = bgimage_read(path, PDF_MAX_BYTES, &len);
    if (!data) return PDF_ERR_READ;
    if (len < 8 || memcmp(data, "%PDF-", 5)) {
        free(data);
        why_set(why, "not a PDF");
        return PDF_ERR_FORMAT;
    }
    PdfReader *r = calloc(1, sizeof *r);
    if (!r) {
        free(data);
        why_set(why, "out of memory");
        return PDF_ERR_MEM;
    }
    r->data = data;
    r->len = len;
    scan_objects(r);
    Rng catalog, pages;
    if (find_catalog(r, &catalog) && dict_get(&catalog, "/Pages", &pages)) {
        int root;  // (a real PDF names its page tree's root here; an inline one is none)
        if (ref_num(&pages, &root)) walk_pages(r, root, 0);
    }
    if (!r->npages) {  // no catalog this reader can follow: the file's Pages nodes as they come
        for (int i = 0; i < r->nobj && !r->npages; i++) {
            Rng d;
            if (!obj_dict(r, r->obj[i].num, &d)) continue;
            char type[24];
            if (!dict_name(r, &d, "/Type", type, sizeof type) || strcmp(type, "Pages")) continue;
            Rng parent;
            if (dict_get(&d, "/Parent", &parent)) continue;  // a child node: its root comes first
            walk_pages(r, r->obj[i].num, 0);
        }
    }
    if (!r->npages) {
        pdf_close(r);
        why_set(why, "no pages this reader can find");
        return PDF_ERR_FORMAT;
    }
    *out = r;
    *npages = r->npages;
    return PDF_OK;
}

void pdf_close(PdfReader *r) {
    if (!r) return;
    free(r->data);
    free(r->obj);
    free(r->pages);
    free(r);
}

// ---- pictures ----

enum { CS_GRAY = 1, CS_RGB = 3, CS_CMYK = 4 };

typedef struct {
    int comps;  // samples a pixel has (1 for an indexed picture, read through pal)
    int kind;   // what those samples become: CS_GRAY, CS_RGB or CS_CMYK
    uint8_t *pal;
    size_t pallen;
    int palcomp;  // the palette's components a step: 1 or 3
} Color;

static bool is_name(const Rng *v, const char *s) {
    char buf[32];
    span_name(v, buf, sizeof buf);
    return buf[0] && !strcmp(buf, s);
}

// A literal or hex string's bytes (a copy the caller frees), or NULL.
static uint8_t *span_string(const Rng *v, size_t *len) {
    *len = 0;
    if (!v->p || v->e <= v->p) return NULL;
    if (*v->p == '(') {
        uint8_t *out = malloc((size_t)(v->e - v->p));
        if (!out) return NULL;
        size_t n = 0;
        for (const uint8_t *p = v->p + 1; p < v->e - 1; p++) {
            uint8_t c = *p;
            if (c == '\\' && p + 1 < v->e - 1) {
                p++;
                switch (*p) {
                case 'n': c = '\n'; break;
                case 'r': c = '\r'; break;
                case 't': c = '\t'; break;
                case 'b': c = '\b'; break;
                case 'f': c = '\f'; break;
                case '\n': continue;
                case '\r':
                    if (p + 1 < v->e - 1 && p[1] == '\n') p++;
                    continue;
                default:
                    if (*p >= '0' && *p <= '7') {
                        int val = *p - '0';
                        for (int k = 0; k < 2 && p + 1 < v->e - 1 && p[1] >= '0' && p[1] <= '7'; k++) val = val * 8 + (*++p - '0');
                        c = (uint8_t)val;
                    } else {
                        c = *p;
                    }
                }
            }
            out[n++] = c;
        }
        *len = n;
        return out;
    }
    if (*v->p == '<') {
        size_t digits = 0;
        for (const uint8_t *p = v->p + 1; p < v->e && *p != '>'; p++)
            if (!is_ws(*p)) digits++;
        size_t n = digits / 2 + (digits & 1);
        uint8_t *out = malloc(n ? n : 1);
        if (!out) return NULL;
        size_t k = 0;
        int hi = -1;
        for (const uint8_t *p = v->p + 1; p < v->e && *p != '>'; p++) {
            int d;
            if (*p >= '0' && *p <= '9') d = *p - '0';
            else if (*p >= 'a' && *p <= 'f') d = *p - 'a' + 10;
            else if (*p >= 'A' && *p <= 'F') d = *p - 'A' + 10;
            else continue;
            if (hi < 0) {
                hi = d;
            } else {
                out[k++] = (uint8_t)(hi * 16 + d);
                hi = -1;
            }
        }
        if (hi >= 0) out[k++] = (uint8_t)(hi * 16);
        *len = k;
        return out;
    }
    return NULL;
}

// What a picture's /ColorSpace says: the samples a pixel has, and what they become. 0 for one this
// reader does not follow (Separation, DeviceN, Pattern).
static int colorspace(const PdfReader *r, Rng cs, Color *c) {
    memset(c, 0, sizeof *c);
    for (int depth = 0; depth < 4; depth++) {
        if (!deref(r, &cs, 0)) return 0;
        if (!is_array(&cs)) {
            if (is_name(&cs, "DeviceGray") || is_name(&cs, "G") || is_name(&cs, "CalGray")) {
                c->comps = c->kind = 1;
                return 1;
            }
            if (is_name(&cs, "DeviceRGB") || is_name(&cs, "RGB") || is_name(&cs, "CalRGB")) {
                c->comps = c->kind = 3;
                return 1;
            }
            if (is_name(&cs, "DeviceCMYK") || is_name(&cs, "CMYK")) {
                c->comps = 4;
                c->kind = CS_CMYK;
                return 1;
            }
            return 0;
        }
        const uint8_t *p = cs.p + 1, *e = cs.e - 1;
        Rng item[5];
        int n = 0;
        while (n < 5 && arr_next(&p, e, &item[n])) n++;
        if (n < 1) return 0;
        char family[32];
        span_name(&item[0], family, sizeof family);
        if (!strcmp(family, "ICCBased") && n >= 2) {  // the profile's stream says how many
            Rng prof = item[1];
            if (!deref(r, &prof, 0) || !is_dict(&prof)) return 0;
            long nn = 0;
            if (!dict_long(r, &prof, "/N", &nn)) return 0;
            if (nn == 1) {
                c->comps = c->kind = 1;
                return 1;
            }
            if (nn == 3) {
                c->comps = c->kind = 3;
                return 1;
            }
            if (nn == 4) {
                c->comps = 4;
                c->kind = CS_CMYK;
                return 1;
            }
            return 0;
        }
        if (!strcmp(family, "CalRGB")) {
            c->comps = c->kind = 3;
            return 1;
        }
        if (!strcmp(family, "CalGray")) {
            c->comps = c->kind = 1;
            return 1;
        }
        if ((!strcmp(family, "Indexed") || !strcmp(family, "I")) && n >= 4) {
            Color base = {0};
            if (!colorspace(r, item[1], &base) || base.pal) return 0;  // (no indexed of an indexed)
            Rng lk = item[3];
            if (!deref(r, &lk, 0)) return 0;
            uint8_t *pal = span_string(&lk, &c->pallen);
            if (!pal) return 0;
            c->pal = pal;
            c->palcomp = base.kind == CS_GRAY ? 1 : 3;
            c->comps = 1;
            c->kind = base.kind;
            return 1;
        }
        return 0;
    }
    return 0;
}

static uint8_t *inflate_to(const uint8_t *src, size_t len, size_t cap, size_t *got) {
    *got = 0;
    if (len == 0 || len > (size_t)INT_MAX || cap == 0 || cap > (size_t)INT_MAX) return NULL;
    uint8_t *out = malloc(cap);
    if (!out) return NULL;
    int n = stbi_zlib_decode_buffer((char *)out, (int)cap, (const char *)src, (int)len);
    if (n <= 0) {
        free(out);
        return NULL;
    }
    *got = (size_t)n;
    return out;
}

static int paeth(int a, int b, int c) {
    int p = a + b - c, pa = abs(p - a), pb = abs(p - b), pc = abs(p - c);
    if (pa <= pb && pa <= pc) return a;
    if (pb <= pc) return b;
    return c;
}

// A row of PNG predictors undone (Predictor 10 to 15), in place, into dst (rowbytes a row).
static void unfilter_row(uint8_t *dst, const uint8_t *src, size_t rowbytes, int kind, const uint8_t *prev, int bpp) {
    for (size_t i = 0; i < rowbytes; i++) {
        int x = src[i];
        int left = i >= (size_t)bpp ? dst[i - (size_t)bpp] : 0;
        int up = prev ? prev[i] : 0;
        int upleft = prev && i >= (size_t)bpp ? prev[i - (size_t)bpp] : 0;
        switch (kind) {
        case 1: x += left; break;
        case 2: x += up; break;
        case 3: x += (left + up) / 2; break;
        case 4: x += paeth(left, up, upleft); break;
        default: break;
        }
        dst[i] = (uint8_t)x;
    }
}

// Samples as they are (after no filter, Flate, and its predictor undone) into 8-bit components.
static uint8_t *unpack(const uint8_t *src, size_t len, int w, int h, int ncomp, int bpc, char *why) {
    size_t rowbytes = ((size_t)w * (size_t)ncomp * (size_t)bpc + 7) / 8;
    if (rowbytes == 0 || (size_t)h > len / rowbytes) {  // (a file that says less than its rows hold)
        why_set(why, "the page picture is short");
        return NULL;
    }
    uint8_t *out = malloc((size_t)w * (size_t)h * (size_t)ncomp);
    if (!out) {
        why_set(why, "out of memory");
        return NULL;
    }
    for (int y = 0; y < h; y++) {
        const uint8_t *row = src + (size_t)y * rowbytes;
        uint8_t *o = out + (size_t)y * (size_t)w * (size_t)ncomp;
        if (bpc == 8) {
            memcpy(o, row, (size_t)w * (size_t)ncomp);
            continue;
        }
        int mask = (1 << bpc) - 1, max = mask;
        size_t bit = 0;
        for (int x = 0; x < w; x++)
            for (int c = 0; c < ncomp; c++) {
                int v;
                if (bpc == 1) {
                    v = (row[bit >> 3] >> (7 - (bit & 7))) & 1;
                } else {
                    size_t byte = bit >> 3;
                    int shift = 8 - bpc - (int)(bit & 7);
                    v = (row[byte] >> shift) & mask;
                    if (shift < 0) v = 0;
                }
                bit += (size_t)bpc;
                o[(size_t)x * ncomp + c] = (uint8_t)(v * 255 / max);
            }
    }
    return out;
}

// The page's samples into a picture: gray, RGB, CMYK turned to RGB, or through an indexed palette.
static int samples_picture(uint8_t *samples, int w, int h, const Color *c, BgPicture *out, char *why) {
    int ncomp = c->comps;
    int ch = c->kind == CS_GRAY ? 1 : 3;
    size_t n = (size_t)w * (size_t)h;
    uint8_t *px = malloc(n * (size_t)ch);
    if (!px) {
        free(samples);
        why_set(why, "out of memory");
        return PDF_ERR_MEM;
    }
    for (size_t i = 0; i < n; i++) {
        const uint8_t *s = samples + i * (size_t)ncomp;
        uint8_t rgb[3];
        if (c->pal) {
            size_t step = (size_t)c->palcomp;
            size_t at = (size_t)s[0] * step;
            if (at + step > c->pallen || !c->pal) {
                rgb[0] = rgb[1] = rgb[2] = 255;
            } else if (step == 1) {
                rgb[0] = rgb[1] = rgb[2] = c->pal[at];
            } else {
                rgb[0] = c->pal[at];
                rgb[1] = c->pal[at + 1];
                rgb[2] = c->pal[at + 2];
            }
        } else if (ncomp == 1) {
            rgb[0] = rgb[1] = rgb[2] = s[0];
        } else if (ncomp == 3) {
            rgb[0] = s[0];
            rgb[1] = s[1];
            rgb[2] = s[2];
        } else {  // CMYK: ink over white paper
            int k = 255 - s[3];
            rgb[0] = (uint8_t)((255 - s[0]) * k / 255);
            rgb[1] = (uint8_t)((255 - s[1]) * k / 255);
            rgb[2] = (uint8_t)((255 - s[2]) * k / 255);
        }
        if (ch == 1) {
            px[i] = rgb[0];
        } else {
            memcpy(px + i * 3, rgb, 3);
        }
    }
    free(samples);
    out->px = px;
    out->w = w;
    out->h = h;
    out->ch = ch;
    return PDF_OK;
}

static bool is_flate(const char *f) { return !strcmp(f, "FlateDecode") || !strcmp(f, "Fl"); }
static bool is_dct(const char *f) { return !strcmp(f, "DCTDecode") || !strcmp(f, "DCT"); }

// How many names /Filter has, into f (at most 3).
static int filters_of(const PdfReader *r, const Rng *d, char f[3][24]) {
    Rng v;
    int n = 0;
    if (!dict_get(d, "/Filter", &v) || !deref(r, &v, 0)) return 0;
    if (!is_array(&v)) {
        span_name(&v, f[0], 24);
        return f[0][0] ? 1 : 0;
    }
    const uint8_t *p = v.p + 1, *e = v.e - 1;
    Rng item;
    while (n < 3 && arr_next(&p, e, &item)) {
        Rng x = item;
        if (!deref(r, &x, 0)) continue;
        span_name(&x, f[n], 24);
        if (f[n][0]) n++;
    }
    return n;
}

// Decodes one image XObject (its dictionary and stream) into a picture.
static int decode_image(const PdfReader *r, const Rng *d, const uint8_t *s, size_t sl, BgPicture *out,
                        char *why) {
    memset(out, 0, sizeof *out);
    long W = 0, H = 0, bpc = 8;
    if (!dict_long(r, d, "/Width", &W) || !dict_long(r, d, "/Height", &H) || W <= 0 || H <= 0 || W > 40000 || H > 40000) {
        why_set(why, "the page picture has no size");
        return PDF_ERR_FORMAT;
    }
    if ((long long)W * H > PDF_MAX_PIXELS) {
        why_set(why, "the page picture is too big");
        return PDF_ERR_UNSUPPORTED;
    }
    Rng maskv;
    if (dict_get(d, "/ImageMask", &maskv)) {  // (a stencil, not a page: 0 paints, 1 is clear)
        long v = 0;
        if (!deref(r, &maskv, 0) || !span_long(&maskv, &v) || v != 0) {
            why_set(why, "the page picture is a mask");
            return PDF_ERR_UNSUPPORTED;
        }
    }
    if (!dict_long(r, d, "/BitsPerComponent", &bpc)) bpc = 8;
    if (bpc != 1 && bpc != 2 && bpc != 4 && bpc != 8) {
        why_set(why, "%ld bits a sample is not read", bpc);
        return PDF_ERR_UNSUPPORTED;
    }
    Rng csv;
    Color color;
    memset(&color, 0, sizeof color);
    if (dict_get(d, "/ColorSpace", &csv)) {
        if (!colorspace(r, csv, &color)) {
            why_set(why, "the page picture's colour is not read");
            return PDF_ERR_UNSUPPORTED;
        }
    } else {
        color.comps = color.kind = 1;
    }
    char f[3][24];
    int nf = filters_of(r, d, f);
    int flate = -1, dct = -1;
    for (int i = 0; i < nf; i++) {
        if (is_flate(f[i]) && flate < 0) flate = i;
        else if (is_dct(f[i]) && dct < 0) dct = i;
        else {
            why_set(why, "%s is not read", f[i]);
            return PDF_ERR_UNSUPPORTED;
        }
    }
    // A JPEG in the file as it is (or after Flate): bgimage_decode reads it, its own checks and all.
    if (dct >= 0) {
        const uint8_t *jp = s;
        size_t jl = sl;
        uint8_t *tmp = NULL;
        if (flate >= 0) {
            if (dct < flate) {
                why_set(why, "the page picture's filters are not read");
                return PDF_ERR_UNSUPPORTED;
            }
            size_t cap = sl + (sl >> 1) + (1u << 20);
            if (cap > PDF_MAX_SAMPLES) cap = PDF_MAX_SAMPLES;
            tmp = inflate_to(s, sl, cap, &jl);
            if (!tmp) {
                why_set(why, "the page picture does not read");
                return PDF_ERR_FORMAT;
            }
            jp = tmp;
        }
        const char *why2 = "the picture does not read";
        int rc = bgimage_decode(jp, jl, out, &why2);
        free(tmp);
        if (rc != 0) {
            why_set(why, "%s", why2);
            return rc == -2 ? PDF_ERR_MEM : PDF_ERR_FORMAT;
        }
        return PDF_OK;
    }
    // Raw samples: Flate, or as they are.
    size_t rowbytes = 0, need = 0;
    int pred = 1, pcolors = color.comps, pbits = (int)bpc, pcols = (int)W;
    {
        Rng parms;
        if (dict_get(d, "/DecodeParms", &parms)) {
            Rng one = parms;
            if (is_array(&one)) {
                const uint8_t *p = one.p + 1, *e = one.e - 1;
                Rng item;
                if (!arr_next(&p, e, &item)) item = (Rng){NULL, NULL};
                one = item;
            }
            if (deref(r, &one, 0) && is_dict(&one)) {
                long v = 1;
                if (dict_long(r, &one, "/Predictor", &v)) pred = (int)v;
                if (dict_long(r, &one, "/Colors", &v)) pcolors = (int)v;
                if (dict_long(r, &one, "/BitsPerComponent", &v)) pbits = (int)v;
                if (dict_long(r, &one, "/Columns", &v)) pcols = (int)v;
            }
        }
        if (pcols <= 0 || pcolors <= 0 || (pbits != 1 && pbits != 2 && pbits != 4 && pbits != 8) || pcols > 40000) {
            why_set(why, "the page picture's rows are not read");
            return PDF_ERR_UNSUPPORTED;
        }
        rowbytes = ((size_t)pcols * (size_t)pcolors * (size_t)pbits + 7) / 8;
        if (rowbytes == 0) {
            why_set(why, "the page picture's rows are empty");
            return PDF_ERR_FORMAT;
        }
        size_t rows = (size_t)H;
        need = rowbytes * rows + (pred >= 10 ? rows : 0);
        if (need > PDF_MAX_SAMPLES) {
            why_set(why, "the page picture is too big");
            return PDF_ERR_UNSUPPORTED;
        }
    }
    uint8_t *raw = NULL, *owned = NULL;
    size_t rawlen = 0;
    if (flate >= 0) {
        owned = inflate_to(s, sl, need + 4096, &rawlen);
        if (!owned) {
            why_set(why, "the page picture does not read");
            return PDF_ERR_FORMAT;
        }
        raw = owned;
    } else {
        raw = (uint8_t *)s;
        rawlen = sl;
    }
    // A row's own filter (PNG predictors, or TIFF's differencing) undone.
    uint8_t *samples = raw;
    uint8_t *rows_buf = NULL;
    if (pred >= 10) {
        int bpp = (pcolors * pbits + 7) / 8;
        if (bpp < 1) bpp = 1;
        if (rawlen < rowbytes * (size_t)H + (size_t)H) {
            free(owned);
            why_set(why, "the page picture is short");
            return PDF_ERR_FORMAT;
        }
        rows_buf = malloc(rowbytes * (size_t)H + rowbytes);
        if (!rows_buf) {
            free(owned);
            why_set(why, "out of memory");
            return PDF_ERR_MEM;
        }
        const uint8_t *prev = NULL;
        for (size_t y = 0; y < (size_t)H; y++) {
            const uint8_t *src = raw + y * (rowbytes + 1);
            uint8_t *dst = rows_buf + y * rowbytes;
            int kind = *src;
            unfilter_row(dst, src + 1, rowbytes, kind, prev, bpp);
            prev = dst;
        }
        samples = rows_buf;
    } else if (pred == 2) {  // TIFF's horizontal differencing
        rows_buf = malloc(rowbytes * (size_t)H);
        if (!rows_buf) {
            free(owned);
            why_set(why, "out of memory");
            return PDF_ERR_MEM;
        }
        memcpy(rows_buf, raw, rawlen < rowbytes * (size_t)H ? rawlen : rowbytes * (size_t)H);
        for (size_t y = 0; y < (size_t)H; y++)
            for (size_t i = 1; i < rowbytes; i++) rows_buf[y * rowbytes + i] += rows_buf[y * rowbytes + i - 1];
        samples = rows_buf;
    }
    uint8_t *packed = unpack(samples, rawlen, (int)W, (int)H, color.comps, (int)bpc, why);
    free(rows_buf);
    free(owned);
    if (!packed) return PDF_ERR_FORMAT;
    int rc = samples_picture(packed, (int)W, (int)H, &color, out, why);
    free(color.pal);
    return rc;
}

// The page's biggest picture: an image XObject of its resources, or of a form's resources.
static bool scan_xobj(const PdfReader *r, Rng xo, int depth, long *best, Rng *best_d, const uint8_t **best_s,
                      size_t *best_sl) {
    if (depth > 3 || !is_dict(&xo)) return false;
    const uint8_t *p = xo.p + 2, *e = xo.e - 2;
    Rng key, val;
    while (dict_next(&p, e, &key, &val)) {
        int num;
        if (!ref_num(&val, &num)) continue;
        Rng d;
        const uint8_t *s = NULL;
        size_t sl = 0;
        bool streamed = false;
        if (!obj_parse(r, obj_find(r, num), &d, &s, &sl, &streamed) || !is_dict(&d)) continue;
        char sub[32];
        if (!dict_name(r, &d, "/Subtype", sub, sizeof sub)) continue;
        if (!strcmp(sub, "Image")) {
            long W = 0, H = 0;
            if (!dict_long(r, &d, "/Width", &W) || !dict_long(r, &d, "/Height", &H)) continue;
            if (W <= 0 || H <= 0 || W > 40000 || H > 40000) continue;
            long area = W * H;
            if (area > *best && streamed) {
                *best = area;
                *best_d = d;
                *best_s = s;
                *best_sl = sl;
            }
        } else if (!strcmp(sub, "Form")) {
            Rng fres, fxo;
            if (dict_get(&d, "/Resources", &fres) && deref(r, &fres, 0) && dict_get(&fres, "/XObject", &fxo) &&
                deref(r, &fxo, 0))
                scan_xobj(r, fxo, depth + 1, best, best_d, best_s, best_sl);
        }
    }
    return *best > 0;
}

static bool page_image(const PdfReader *r, Rng page, Rng *img, const uint8_t **s, size_t *sl) {
    Rng res, xo;
    if (!inherited(r, page, "/Resources", &res) || !deref(r, &res, 0)) return false;
    if (!dict_get(&res, "/XObject", &xo) || !deref(r, &xo, 0)) return false;
    long best = 0;
    return scan_xobj(r, xo, 0, &best, img, s, sl);
}

// ---- turning, and down to the size the notebook keeps ----

static int rotate_picture(BgPicture *p, int deg) {
    deg = ((deg % 360) + 360) % 360;
    if (!p->px || deg == 0) return 0;
    int w = p->w, h = p->h, ch = p->ch;
    int nw = deg == 180 ? w : h, nh = deg == 180 ? h : w;
    uint8_t *px = malloc((size_t)nw * (size_t)nh * (size_t)ch);
    if (!px) return -1;
    for (int dy = 0; dy < nh; dy++)
        for (int dx = 0; dx < nw; dx++) {
            int sx, sy;
            if (deg == 90) {  // a quarter turn clockwise
                sx = dy;
                sy = h - 1 - dx;
            } else if (deg == 180) {
                sx = w - 1 - dx;
                sy = h - 1 - dy;
            } else {  // 270
                sx = w - 1 - dy;
                sy = dx;
            }
            memcpy(px + ((size_t)dy * (size_t)nw + (size_t)dx) * (size_t)ch,
                   p->px + ((size_t)sy * (size_t)w + (size_t)sx) * (size_t)ch, (size_t)ch);
        }
    free(p->px);
    p->px = px;
    p->w = nw;
    p->h = nh;
    return 0;
}

// The picture averaged down to at most max_w x max_h (whole blocks, as bgimage_normalize does).
static void shrink_picture(BgPicture *p, int max_w, int max_h) {
    if (!p->px || max_w < 1 || max_h < 1) return;
    int f = 1;
    while ((p->w + f - 1) / f > max_w || (p->h + f - 1) / f > max_h) f++;
    if (f <= 1) return;
    int nw = (p->w + f - 1) / f, nh = (p->h + f - 1) / f, ch = p->ch;
    if (nw < 1) nw = 1;
    if (nh < 1) nh = 1;
    uint8_t *px = malloc((size_t)nw * (size_t)nh * (size_t)ch);
    if (!px) return;
    for (int y = 0; y < nh; y++)
        for (int x = 0; x < nw; x++) {
            int sum[3] = {0, 0, 0}, n = 0;
            for (int by = y * f; by < (y + 1) * f && by < p->h; by++)
                for (int bx = x * f; bx < (x + 1) * f && bx < p->w; bx++) {
                    for (int c = 0; c < ch; c++) sum[c] += p->px[((size_t)by * (size_t)p->w + (size_t)bx) * (size_t)ch + (size_t)c];
                    n++;
                }
            for (int c = 0; c < ch; c++)
                px[((size_t)y * (size_t)nw + (size_t)x) * (size_t)ch + (size_t)c] = (uint8_t)(n ? sum[c] / n : 255);
        }
    free(p->px);
    p->px = px;
    p->w = nw;
    p->h = nh;
}

int pdf_page_picture(PdfReader *r, int index, int max_w, int max_h, BgPicture *out, char *why) {
    memset(out, 0, sizeof *out);
    if (!r || index < 0 || index >= r->npages) {
        why_set(why, "no such page");
        return PDF_ERR_FORMAT;
    }
    Rng page;
    if (!obj_dict(r, r->pages[index], &page)) {
        why_set(why, "the page does not read");
        return PDF_ERR_FORMAT;
    }
    Rng img;
    const uint8_t *s = NULL;
    size_t sl = 0;
    if (!page_image(r, page, &img, &s, &sl)) {
        why_set(why, "the page is text or line art, not a page picture");
        return PDF_ERR_NO_PICTURE;
    }
    int rc = decode_image(r, &img, s, sl, out, why);
    if (rc != PDF_OK) return rc;
    long rot = 0;
    Rng rv;
    if (inherited(r, page, "/Rotate", &rv) && deref(r, &rv, 0)) span_long(&rv, &rot);
    if (rot % 90 == 0 && rotate_picture(out, (int)rot) != 0) {
        bgpicture_free(out);
        why_set(why, "out of memory");
        return PDF_ERR_MEM;
    }
    shrink_picture(out, max_w, max_h);
    return PDF_OK;
}
