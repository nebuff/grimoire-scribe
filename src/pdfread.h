// pdfread.h: the page pictures of a PDF, for grimoire/import (docs/EXPORT.md).
//
// A PDF is read here only as far as a notebook needs it: each page's picture, the whole page drawn
// as one image, which is what a scan, a photographed page, or a PDF exported from another app
// holds. A page set in fonts and drawn with vector graphics has no such picture: Grimoire leaves
// that PDF alone rather than show it wrong.
//
// Reading runs in the import's forked child (bgwork_template.c), never on the UI thread.
#pragma once
#include "bgimage.h"

#define PDF_WHY_LEN 96

typedef struct PdfReader PdfReader;

// What reading a PDF (or one of its pages) came to.
enum {
    PDF_OK = 0,
    PDF_ERR_READ = -1,         // the file does not read, or is bigger than a PDF Grimoire takes (may pass)
    PDF_ERR_FORMAT = -2,       // not a PDF, or one this reader cannot follow (it will not pass)
    PDF_ERR_NO_PICTURE = -3,   // a page has no whole-page picture (text in fonts, vector graphics)
    PDF_ERR_UNSUPPORTED = -4,  // the picture is in a form Grimoire does not decode (JPEG 2000, CCITT...)
    PDF_ERR_MEM = -5,          // not enough memory (another time there may be)
};

// Opens path for reading its pages' pictures. 0 with *npages and *r (pdf_close frees it), or
// PDF_ERR_READ / PDF_ERR_FORMAT / PDF_ERR_MEM with why set (a short line for grimoire.log).
int pdf_open(const char *path, PdfReader **r, int *npages, char *why);
// Page index (0-based) as a picture of at most max_w x max_h pixels (a bigger one is averaged down),
// 1 (gray) or 3 (RGB) channels. 0 with *out (bgpicture_free frees it), or a PDF_ERR_* with why.
int pdf_page_picture(PdfReader *r, int index, int max_w, int max_h, BgPicture *out, char *why);
void pdf_close(PdfReader *r);
