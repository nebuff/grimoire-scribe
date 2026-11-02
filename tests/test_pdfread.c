// test_pdfread.c: the page pictures of a PDF (src/pdfread.h): the picture a page holds, its
// predictors, its turning, and the pages Grimoire will not show (text set in fonts, masks, JPEG
// 2000), on hand-made PDFs in a scratch folder.
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include "pdfread.h"
#include "testlib.h"

// stb_image_write's deflate (stb_impl.c), for the Flate streams a PDF holds.
unsigned char *stbi_zlib_compress(unsigned char *data, int data_len, int *out_len, int quality);

static char dir[600];

static const char *put_pdf(const char *name, const uint8_t *buf, size_t n) {
    static char path[700];
    snprintf(path, sizeof path, "%s/%s", dir, name);
    FILE *f = fopen(path, "wb");
    CHECK(f != NULL);
    if (f) {
        CHECK(fwrite(buf, 1, n, f) == n);
        fclose(f);
    }
    return path;
}

// One page holding one image: the image's stream already compressed, the page's colour space and
// bits a sample, and any other keys of the page's dictionary ("/Rotate 90").
static size_t make_pdf(uint8_t *out, size_t cap, int w, int h, const uint8_t *img, size_t imglen, const char *cs,
                       int bpc, const char *extra) {
    size_t n = 0;
    n += (size_t)snprintf((char *)out + n, cap - n, "%%PDF-1.4\n");
    n += (size_t)snprintf((char *)out + n, cap - n, "1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n");
    n += (size_t)snprintf((char *)out + n, cap - n, "2 0 obj\n<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n");
    n += (size_t)snprintf((char *)out + n, cap - n,
                          "3 0 obj\n<< /Type /Page /Parent 2 0 R /Resources << /XObject << /Im0 4 0 R >> >> %s >>\n"
                          "endobj\n",
                          extra ? extra : "");
    n += (size_t)snprintf((char *)out + n, cap - n,
                          "4 0 obj\n<< /Type /XObject /Subtype /Image /Width %d /Height %d /ColorSpace %s "
                          "/BitsPerComponent %d /Filter /FlateDecode /Length %zu >>\nstream\n",
                          w, h, cs, bpc, imglen);
    memcpy(out + n, img, imglen);
    n += imglen;
    n += (size_t)snprintf((char *)out + n, cap - n, "\nendstream\nendobj\ntrailer\n<< /Root 1 0 R >>\n%%%%EOF\n");
    return n;
}

// A page of text: its content is a stream of text operators, and it has no image at all.
static size_t make_text_pdf(uint8_t *out, size_t cap) {
    size_t n = 0;
    n += (size_t)snprintf((char *)out + n, cap - n, "%%PDF-1.4\n");
    n += (size_t)snprintf((char *)out + n, cap - n, "1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n");
    n += (size_t)snprintf((char *)out + n, cap - n, "2 0 obj\n<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n");
    n += (size_t)snprintf((char *)out + n, cap - n,
                          "3 0 obj\n<< /Type /Page /Parent 2 0 R /Contents 4 0 R >>\nendobj\n");
    n += (size_t)snprintf((char *)out + n, cap - n,
                          "4 0 obj\n<< /Length 26 >>\nstream\nBT /F1 12 Tf (hi) Tj ET\nendstream\nendobj\n"
                          "trailer\n<< /Root 1 0 R >>\n%%%%EOF\n");
    return n;
}

static const uint8_t *deflate(const uint8_t *raw, size_t n, size_t *outlen) {
    int zl = 0;
    unsigned char *z = stbi_zlib_compress((unsigned char *)raw, (int)n, &zl, 0);
    CHECK(z && zl > 0);
    *outlen = (size_t)(zl > 0 ? zl : 0);
    return z;
}

TEST(not_a_pdf) {
    const char *path = put_pdf("notes.txt", (const uint8_t *)"hello", 5);
    PdfReader *r = NULL;
    int np = 0;
    char why[PDF_WHY_LEN];
    CHECK(pdf_open(path, &r, &np, why) == PDF_ERR_FORMAT);
    CHECK(r == NULL && np == 0 && why[0]);
}

TEST(gray_page) {
    uint8_t raw[16];
    for (int i = 0; i < 16; i++) raw[i] = (uint8_t)(i * 16);
    size_t zl;
    const uint8_t *z = deflate(raw, sizeof raw, &zl);
    uint8_t pdf[4096];
    size_t n = make_pdf(pdf, sizeof pdf, 4, 4, z, zl, "/DeviceGray", 8, NULL);
    free((void *)z);
    const char *path = put_pdf("gray.pdf", pdf, n);
    PdfReader *r = NULL;
    int np = 0;
    char why[PDF_WHY_LEN];
    CHECK(pdf_open(path, &r, &np, why) == PDF_OK);
    CHECK(np == 1);
    BgPicture p;
    CHECK(pdf_page_picture(r, 0, 1000, 1000, &p, why) == PDF_OK);
    CHECK(p.w == 4 && p.h == 4 && p.ch == 1);
    for (int i = 0; i < 16; i++) CHECK(p.px[i] == (uint8_t)(i * 16));
    bgpicture_free(&p);
    pdf_close(r);
}

TEST(bilevel_page) {
    // 8 x 2, a byte a row: four black then four white, then the other way round.
    uint8_t raw[2] = {0x0F, 0xF0};
    size_t zl;
    const uint8_t *z = deflate(raw, sizeof raw, &zl);
    uint8_t pdf[4096];
    size_t n = make_pdf(pdf, sizeof pdf, 8, 2, z, zl, "/DeviceGray", 1, NULL);
    free((void *)z);
    const char *path = put_pdf("bilevel.pdf", pdf, n);
    PdfReader *r = NULL;
    int np = 0;
    char why[PDF_WHY_LEN];
    CHECK(pdf_open(path, &r, &np, why) == PDF_OK);
    BgPicture p;
    CHECK(pdf_page_picture(r, 0, 1000, 1000, &p, why) == PDF_OK);
    CHECK(p.w == 8 && p.h == 2 && p.ch == 1);
    CHECK(p.px[0] == 0 && p.px[3] == 0 && p.px[4] == 255 && p.px[7] == 255);
    CHECK(p.px[8] == 255 && p.px[11] == 255 && p.px[12] == 0 && p.px[15] == 0);
    bgpicture_free(&p);
    pdf_close(r);
}

TEST(down_to_a_page_size) {
    uint8_t raw[400 * 400];
    memset(raw, 128, sizeof raw);
    size_t zl;
    const uint8_t *z = deflate(raw, sizeof raw, &zl);
    uint8_t *pdf = malloc(1u << 20);
    CHECK(pdf != NULL);
    size_t n = make_pdf(pdf, 1u << 20, 400, 400, z, zl, "/DeviceGray", 8, NULL);
    free((void *)z);
    const char *path = put_pdf("big.pdf", pdf, n);
    free(pdf);
    PdfReader *r = NULL;
    int np = 0;
    char why[PDF_WHY_LEN];
    CHECK(pdf_open(path, &r, &np, why) == PDF_OK);
    BgPicture p;
    CHECK(pdf_page_picture(r, 0, 100, 100, &p, why) == PDF_OK);
    CHECK(p.w == 100 && p.h == 100);
    CHECK(p.px[0] == 128 && p.px[100 * 99 + 99] == 128);
    bgpicture_free(&p);
    pdf_close(r);
}

TEST(a_page_turned_a_quarter_turn) {
    uint8_t raw[2] = {0, 200};
    size_t zl;
    const uint8_t *z = deflate(raw, sizeof raw, &zl);
    uint8_t pdf[4096];
    size_t n = make_pdf(pdf, sizeof pdf, 2, 1, z, zl, "/DeviceGray", 8, "/Rotate 90");
    free((void *)z);
    const char *path = put_pdf("turned.pdf", pdf, n);
    PdfReader *r = NULL;
    int np = 0;
    char why[PDF_WHY_LEN];
    CHECK(pdf_open(path, &r, &np, why) == PDF_OK);
    BgPicture p;
    CHECK(pdf_page_picture(r, 0, 1000, 1000, &p, why) == PDF_OK);
    CHECK(p.w == 1 && p.h == 2 && p.ch == 1);
    CHECK(p.px[0] == 0 && p.px[1] == 200);
    bgpicture_free(&p);
    pdf_close(r);
}

TEST(text_page_has_no_picture) {
    uint8_t pdf[4096];
    size_t n = make_text_pdf(pdf, sizeof pdf);
    const char *path = put_pdf("text.pdf", pdf, n);
    PdfReader *r = NULL;
    int np = 0;
    char why[PDF_WHY_LEN];
    CHECK(pdf_open(path, &r, &np, why) == PDF_OK);
    CHECK(np == 1);
    BgPicture p;
    CHECK(pdf_page_picture(r, 0, 1000, 1000, &p, why) == PDF_ERR_NO_PICTURE);
    CHECK(p.px == NULL && why[0]);
    pdf_close(r);
}

TEST(a_missing_file) {
    PdfReader *r = NULL;
    int np = 0;
    char why[PDF_WHY_LEN];
    CHECK(pdf_open("/nonexistent/none.pdf", &r, &np, why) == PDF_ERR_READ);
    CHECK(r == NULL && np == 0);
}

int main(void) {
    snprintf(dir, sizeof dir, "%s/pdfread-%d", tl_tmp(), (int)getpid());
    char cmd[700];
    snprintf(cmd, sizeof cmd, "rm -rf '%s'", dir);
    system(cmd);
    CHECK(mkdir(dir, 0700) == 0);
    RUN(not_a_pdf);
    RUN(gray_page);
    RUN(bilevel_page);
    RUN(down_to_a_page_size);
    RUN(a_page_turned_a_quarter_turn);
    RUN(text_page_has_no_picture);
    RUN(a_missing_file);
    int rc = tl_done();
    system(cmd);
    return rc;
}
