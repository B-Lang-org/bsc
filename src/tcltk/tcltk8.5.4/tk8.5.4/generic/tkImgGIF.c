/*
 * tkImgGIF.c --
 *
 *	A photo image file handler for GIF files. Reads 87a and 89a GIF files.
 *	At present, there only is a file write function. GIF images may be
 *	read using the -data option of the photo image. The data may be given
 *	as a binary string in a Tcl_Obj or by representing the data as BASE64
 *	encoded ascii. Derived from the giftoppm code found in the pbmplus
 *	package and tkImgFmtPPM.c in the tk4.0b2 distribution.
 *
 * Copyright (c) Reed Wade (wade@cs.utk.edu), University of Tennessee
 * Copyright (c) 1995-1997 Sun Microsystems, Inc.
 * Copyright (c) 1997 Australian National University
 * Copyright (c) 2005 Donal K. Fellows
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * This file also contains code from the giftoppm program, which is
 * copyrighted as follows:
 *
 * +--------------------------------------------------------------------+
 * | Copyright 1990, David Koblas.					|
 * |   Permission to use, copy, modify, and distribute this software	|
 * |   and its documentation for any purpose and without fee is hereby	|
 * |   granted, provided that the above copyright notice appear in all	|
 * |   copies and that both that copyright notice and this permission	|
 * |   notice appear in supporting documentation. This software is	|
 * |   provided "as is" without express or implied warranty.		|
 * +--------------------------------------------------------------------+
 *
 * This file also contains code from miGIF. See lower down in file for the
 * applicable copyright notice for that portion.
 *
 * RCS: @(#) $Id: tkImgGIF.c,v 1.41 2008/02/01 16:53:53 rmax Exp $
 */

#include "tkInt.h"

/*
 * GIF's are represented as data in either binary or base64 format. base64
 * strings consist of 4 6-bit characters -> 3 8 bit bytes. A-Z, a-z, 0-9, +
 * and / represent the 64 values (in order). '=' is a trailing padding char
 * when the un-encoded data is not a multiple of 3 bytes. We'll ignore white
 * space when encountered. Any other invalid character is treated as an EOF
 */

#define GIF_SPECIAL	(256)
#define GIF_PAD		(GIF_SPECIAL+1)
#define GIF_SPACE	(GIF_SPECIAL+2)
#define GIF_BAD		(GIF_SPECIAL+3)
#define GIF_DONE	(GIF_SPECIAL+4)

/*
 * structure to "mimic" FILE for Mread, so we can look like fread. The decoder
 * state keeps track of which byte we are about to read, or EOF.
 */

typedef struct mFile {
    unsigned char *data;	/* mmencoded source string */
    int c;			/* bits left over from previous character */
    int state;			/* decoder state (0-4 or GIF_DONE) */
    int length;			/* Total amount of bytes in data */
} MFile;

/*
 * Non-ASCII encoding support:
 * Most data in a GIF image is binary and is treated as such. However, a few
 * key bits are stashed in ASCII. If we try to compare those pieces to the
 * char they represent, it will fail on any non-ASCII (eg, EBCDIC) system. To
 * accomodate these systems, we test against the numeric value of the ASCII
 * characters instead of the characters themselves. This is encoding
 * independant.
 */

static const char GIF87a[] = {			/* ASCII GIF87a */
    0x47, 0x49, 0x46, 0x38, 0x37, 0x61, 0x00
};
static const char GIF89a[] = {			/* ASCII GIF89a */
    0x47, 0x49, 0x46, 0x38, 0x39, 0x61, 0x00
};
#define GIF_TERMINATOR	0x3b			/* ASCII ; */
#define GIF_EXTENSION	0x21			/* ASCII ! */
#define GIF_START	0x2c			/* ASCII , */

/*
 * Flags used to notify that we've got inline data instead of a file to read
 * from. Note that we need to figure out which type of inline data we've got
 * before handing off to the GIF reading code; this is done in StringReadGIF.
 */

#define INLINE_DATA_BINARY	((const char *) 0x01)
#define INLINE_DATA_BASE64	((const char *) 0x02)

/*
 *		HACK ALERT!!  HACK ALERT!!  HACK ALERT!!
 * This code is hard-wired for reading from files. In order to read from a
 * data stream, we'll trick fread so we can reuse the same code. 0==from file;
 * 1==from base64 encoded data; 2==from binary data
 */

typedef struct {
    const char *fromData;
    unsigned char workingBuffer[280];
    struct {
	int bytes;
	int done;
	unsigned int window;
	int bitsInWindow;
	unsigned char *c;
    } reader;
} GIFImageConfig;

/*
 * The format record for the GIF file format:
 */

static int		FileMatchGIF(Tcl_Channel chan, const char *fileName,
			    Tcl_Obj *format, int *widthPtr, int *heightPtr,
			    Tcl_Interp *interp);
static int		FileReadGIF(Tcl_Interp *interp, Tcl_Channel chan,
			    const char *fileName, Tcl_Obj *format,
			    Tk_PhotoHandle imageHandle, int destX, int destY,
			    int width, int height, int srcX, int srcY);
static int		StringMatchGIF(Tcl_Obj *dataObj, Tcl_Obj *format,
			    int *widthPtr, int *heightPtr, Tcl_Interp *interp);
static int		StringReadGIF(Tcl_Interp *interp, Tcl_Obj *dataObj,
			    Tcl_Obj *format, Tk_PhotoHandle imageHandle,
			    int destX, int destY, int width, int height,
			    int srcX, int srcY);
static int		FileWriteGIF(Tcl_Interp *interp, const char *filename,
			    Tcl_Obj *format, Tk_PhotoImageBlock *blockPtr);
static int		CommonWriteGIF(Tcl_Interp *interp, Tcl_Channel handle,
			    Tcl_Obj *format, Tk_PhotoImageBlock *blockPtr);

Tk_PhotoImageFormat tkImgFmtGIF = {
    "gif",		/* name */
    FileMatchGIF,	/* fileMatchProc */
    StringMatchGIF,	/* stringMatchProc */
    FileReadGIF,	/* fileReadProc */
    StringReadGIF,	/* stringReadProc */
    FileWriteGIF,	/* fileWriteProc */
    NULL,		/* stringWriteProc */
};

#define INTERLACE		0x40
#define LOCALCOLORMAP		0x80
#define BitSet(byte, bit)	(((byte) & (bit)) == (bit))
#define MAXCOLORMAPSIZE		256
#define CM_RED			0
#define CM_GREEN		1
#define CM_BLUE			2
#define CM_ALPHA		3
#define MAX_LWZ_BITS		12
#define LM_to_uint(a,b)		(((b)<<8)|(a))

/*
 * Prototypes for local functions defined in this file:
 */

static int		DoExtension(GIFImageConfig *gifConfPtr,
			    Tcl_Channel chan, int label, unsigned char *buffer,
			    int *transparent);
static int		GetCode(Tcl_Channel chan, int code_size, int flag,
			    GIFImageConfig *gifConfPtr);
static int		GetDataBlock(GIFImageConfig *gifConfPtr,
			    Tcl_Channel chan, unsigned char *buf);
static int		ReadColorMap(GIFImageConfig *gifConfPtr,
			    Tcl_Channel chan, int number,
			    unsigned char buffer[MAXCOLORMAPSIZE][4]);
static int		ReadGIFHeader(GIFImageConfig *gifConfPtr,
			    Tcl_Channel chan, int *widthPtr, int *heightPtr);
static int		ReadImage(GIFImageConfig *gifConfPtr,
			    Tcl_Interp *interp, unsigned char *imagePtr,
			    Tcl_Channel chan, int len, int rows,
			    unsigned char cmap[MAXCOLORMAPSIZE][4], int srcX,
			    int srcY, int interlace, int transparent);

/*
 * these are for the BASE64 image reader code only
 */

static int		Fread(GIFImageConfig *gifConfPtr, unsigned char *dst,
			    size_t size, size_t count, Tcl_Channel chan);
static int		Mread(unsigned char *dst, size_t size, size_t count,
			    MFile *handle);
static int		Mgetc(MFile *handle);
static int		char64(int c);
static void		mInit(unsigned char *string, MFile *handle,
			    int length);

/*
 *----------------------------------------------------------------------
 *
 * FileMatchGIF --
 *
 *	This function is invoked by the photo image type to see if a file
 *	contains image data in GIF format.
 *
 * Results:
 *	The return value is 1 if the first characters in file f look like GIF
 *	data, and 0 otherwise.
 *
 * Side effects:
 *	The access position in f may change.
 *
 *----------------------------------------------------------------------
 */

static int
FileMatchGIF(
    Tcl_Channel chan,		/* The image file, open for reading. */
    const char *fileName,	/* The name of the image file. */
    Tcl_Obj *format,		/* User-specified format object, or NULL. */
    int *widthPtr, int *heightPtr,
				/* The dimensions of the image are returned
				 * here if the file is a valid raw GIF file. */
    Tcl_Interp *interp)		/* not used */
{
    GIFImageConfig gifConf;

    memset(&gifConf, 0, sizeof(GIFImageConfig));
    return ReadGIFHeader(&gifConf, chan, widthPtr, heightPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * FileReadGIF --
 *
 *	This function is called by the photo image type to read GIF format
 *	data from a file and write it into a given photo image.
 *
 * Results:
 *	A standard TCL completion code. If TCL_ERROR is returned then an error
 *	message is left in the interp's result.
 *
 * Side effects:
 *	The access position in file f is changed, and new data is added to the
 *	image given by imageHandle.
 *
 *----------------------------------------------------------------------
 */

static int
FileReadGIF(
    Tcl_Interp *interp,		/* Interpreter to use for reporting errors. */
    Tcl_Channel chan,		/* The image file, open for reading. */
    const char *fileName,	/* The name of the image file. */
    Tcl_Obj *format,		/* User-specified format object, or NULL. */
    Tk_PhotoHandle imageHandle,	/* The photo image to write into. */
    int destX, int destY,	/* Coordinates of top-left pixel in photo
				 * image to be written to. */
    int width, int height,	/* Dimensions of block of photo image to be
				 * written to. */
    int srcX, int srcY)		/* Coordinates of top-left pixel to be used in
				 * image being read. */
{
    int fileWidth, fileHeight, imageWidth, imageHeight;
    int nBytes, index = 0, argc = 0, i, result = TCL_ERROR;
    Tcl_Obj **objv;
    unsigned char buf[100];
    unsigned char *trashBuffer = NULL;
    int bitPixel;
    unsigned char colorMap[MAXCOLORMAPSIZE][4];
    int transparent = -1;
    static const char *optionStrings[] = {
	"-index", NULL
    };
    GIFImageConfig gifConf, *gifConfPtr = &gifConf;

    /*
     * Decode the magic used to convey when we're sourcing data from a string
     * source and not a file.
     */

    memset(gifConfPtr, 0, sizeof(GIFImageConfig));
    if (fileName == INLINE_DATA_BINARY || fileName == INLINE_DATA_BASE64) {
	gifConfPtr->fromData = fileName;
	fileName = "inline data";
    }

    /*
     * Parse the format string to get options.
     */

    if (format && Tcl_ListObjGetElements(interp, format,
	    &argc, &objv) != TCL_OK) {
	return TCL_ERROR;
    }
    for (i = 1; i < argc; i++) {
	if (Tcl_GetIndexFromObj(interp, objv[i], optionStrings, "option name",
		0, &nBytes) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (i == (argc-1)) {
	    Tcl_AppendResult(interp, "no value given for \"",
		    Tcl_GetString(objv[i]), "\" option", NULL);
	    return TCL_ERROR;
	}
	if (Tcl_GetIntFromObj(interp, objv[++i], &index) != TCL_OK) {
	    return TCL_ERROR;
	}
    }

    /*
     * Read the GIF file header and check for some sanity.
     */

    if (!ReadGIFHeader(gifConfPtr, chan, &fileWidth, &fileHeight)) {
	Tcl_AppendResult(interp, "couldn't read GIF header from file \"",
		fileName, "\"", NULL);
	return TCL_ERROR;
    }
    if ((fileWidth <= 0) || (fileHeight <= 0)) {
	Tcl_AppendResult(interp, "GIF image file \"", fileName,
		"\" has dimension(s) <= 0", NULL);
	return TCL_ERROR;
    }

    /*
     * Get the general colormap information.
     */

    if (Fread(gifConfPtr, buf, 1, 3, chan) != 3) {
	return TCL_OK;
    }
    bitPixel = 2 << (buf[0] & 0x07);

    if (BitSet(buf[0], LOCALCOLORMAP)) {	/* Global Colormap */
	if (!ReadColorMap(gifConfPtr, chan, bitPixel, colorMap)) {
	    Tcl_AppendResult(interp, "error reading color map", NULL);
	    return TCL_ERROR;
	}
    }

    if ((srcX + width) > fileWidth) {
	width = fileWidth - srcX;
    }
    if ((srcY + height) > fileHeight) {
	height = fileHeight - srcY;
    }
    if ((width <= 0) || (height <= 0)
	    || (srcX >= fileWidth) || (srcY >= fileHeight)) {
	return TCL_OK;
    }

    /*
     * Make sure we have enough space in the photo image to hold the data from
     * the GIF.
     */

    if (Tk_PhotoExpand(interp, imageHandle,
	    destX + width, destY + height) != TCL_OK) {
	return TCL_ERROR;
    }

    /*
     * Search for the frame from the GIF to display.
     */

    while (1) {
	if (Fread(gifConfPtr, buf, 1, 1, chan) != 1) {
	    /*
	     * Premature end of image.
	     */

	    Tcl_AppendResult(interp,
		    "premature end of image data for this index", NULL);
	    goto error;
	}

	switch (buf[0]) {
	case GIF_TERMINATOR:
	    Tcl_AppendResult(interp, "no image data for this index", NULL);
	    goto error;

	case GIF_EXTENSION:
	    /*
	     * This is a GIF extension.
	     */

	    if (Fread(gifConfPtr, buf, 1, 1, chan) != 1) {
		Tcl_SetResult(interp,
			"error reading extension function code in GIF image",
			TCL_STATIC);
		goto error;
	    }
	    if (DoExtension(gifConfPtr, chan, buf[0],
		    gifConfPtr->workingBuffer, &transparent) < 0) {
		Tcl_SetResult(interp, "error reading extension in GIF image",
			TCL_STATIC);
		goto error;
	    }
	    continue;
	case GIF_START:
	    if (Fread(gifConfPtr, buf, 1, 9, chan) != 9) {
		Tcl_SetResult(interp,
			"couldn't read left/top/width/height in GIF image",
			TCL_STATIC);
		goto error;
	    }
	    break;
	default:
	    /*
	     * Not a valid start character; ignore it.
	     */

	    continue;
	}

	/*
	 * We've read the header for a GIF frame. Work out what we are going
	 * to do about it.
	 */

	imageWidth = LM_to_uint(buf[4], buf[5]);
	imageHeight = LM_to_uint(buf[6], buf[7]);
	bitPixel = 1 << ((buf[8] & 0x07) + 1);

	if (index--) {
	    /*
	     * This is not the GIF frame we want to read: skip it.
	     */

	    if (BitSet(buf[8], LOCALCOLORMAP)) {
		if (!ReadColorMap(gifConfPtr, chan, bitPixel, colorMap)) {
		    Tcl_AppendResult(interp, "error reading color map", NULL);
		    goto error;
		}
	    }

	    /*
	     * If we've not yet allocated a trash buffer, do so now.
	     */

	    if (trashBuffer == NULL) {
		nBytes = fileWidth * fileHeight * 3;
		trashBuffer = (unsigned char *) ckalloc((unsigned) nBytes);
	    }

	    /*
	     * Slurp! Process the data for this image and stuff it in a trash
	     * buffer.
	     *
	     * Yes, it might be more efficient here to *not* store the data
	     * (we're just going to throw it away later). However, I elected
	     * to implement it this way for good reasons. First, I wanted to
	     * avoid duplicating the (fairly complex) LWZ decoder in
	     * ReadImage. Fine, you say, why didn't you just modify it to
	     * allow the use of a NULL specifier for the output buffer? I
	     * tried that, but it negatively impacted the performance of what
	     * I think will be the common case: reading the first image in the
	     * file. Rather than marginally improve the speed of the less
	     * frequent case, I chose to maintain high performance for the
	     * common case.
	     */

	    if (ReadImage(gifConfPtr, interp, trashBuffer, chan, imageWidth,
		    imageHeight, colorMap, 0, 0, 0, -1) != TCL_OK) {
		goto error;
	    }
	    continue;
	}
	break;
    }

    /*
     * Found the frame we want to read. Next, check for a local color map for
     * this frame.
     */

    if (BitSet(buf[8], LOCALCOLORMAP)) {
	if (!ReadColorMap(gifConfPtr, chan, bitPixel, colorMap)) {
	    Tcl_AppendResult(interp, "error reading color map", NULL);
	    goto error;
	}
    }

    /*
     * Extract the location within the overall visible image to put the data
     * in this frame, together with the size of this frame.
     */

    index = LM_to_uint(buf[0], buf[1]);
    srcX -= index;
    if (srcX<0) {
	destX -= srcX; width += srcX;
	srcX = 0;
    }

    if (width > imageWidth) {
	width = imageWidth;
    }

    index = LM_to_uint(buf[2], buf[3]);
    srcY -= index;
    if (index > srcY) {
	destY -= srcY; height += srcY;
	srcY = 0;
    }
    if (height > imageHeight) {
	height = imageHeight;
    }

    if ((width > 0) && (height > 0)) {
	Tk_PhotoImageBlock block;

	/*
	 * Read the data and put it into the photo buffer for display by the
	 * general image machinery.
	 */

	block.width = width;
	block.height = height;
	block.pixelSize = (transparent>=0) ? 4 : 3;
	block.offset[0] = 0;
	block.offset[1] = 1;
	block.offset[2] = 2;
	block.offset[3] = (transparent>=0) ? 3 : 0;
	block.pitch = block.pixelSize * imageWidth;
	nBytes = block.pitch * imageHeight;
	block.pixelPtr = (unsigned char *) ckalloc((unsigned) nBytes);

	if (ReadImage(gifConfPtr, interp, block.pixelPtr, chan, imageWidth,
		imageHeight, colorMap, srcX, srcY, BitSet(buf[8],INTERLACE),
		transparent) != TCL_OK) {
	    ckfree((char *) block.pixelPtr);
	    goto error;
	}
	if (Tk_PhotoPutBlock(interp, imageHandle, &block, destX, destY,
		width, height, TK_PHOTO_COMPOSITE_SET) != TCL_OK) {
	    ckfree((char *) block.pixelPtr);
	    goto error;
	}
	ckfree((char *) block.pixelPtr);
    }

    /*
     * We've successfully read the GIF frame (or there was nothing to read,
     * which suits as well). We're done.
     */

    Tcl_AppendResult(interp, tkImgFmtGIF.name, NULL);
    result = TCL_OK;

  error:
    /*
     * If a trash buffer has been allocated, free it now.
     */

    if (trashBuffer != NULL) {
	ckfree((char *) trashBuffer);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * StringMatchGIF --
 *
 *	This function is invoked by the photo image type to see if an object
 *	contains image data in GIF format.
 *
 * Results:
 *	The return value is 1 if the first characters in the data are like GIF
 *	data, and 0 otherwise.
 *
 * Side effects:
 *	The size of the image is placed in widthPtr and heightPtr.
 *
 *----------------------------------------------------------------------
 */

static int
StringMatchGIF(
    Tcl_Obj *dataObj,		/* the object containing the image data */
    Tcl_Obj *format,		/* the image format object, or NULL */
    int *widthPtr,		/* where to put the string width */
    int *heightPtr,		/* where to put the string height */
    Tcl_Interp *interp)		/* not used */
{
    unsigned char *data, header[10];
    int got, length;
    MFile handle;

    data = Tcl_GetByteArrayFromObj(dataObj, &length);

    /*
     * Header is a minimum of 10 bytes.
     */

    if (length < 10) {
	return 0;
    }

    /*
     * Check whether the data is Base64 encoded.
     */

    if ((strncmp(GIF87a, (char *) data, 6) != 0) &&
	    (strncmp(GIF89a, (char *) data, 6) != 0)) {
	/*
	 * Try interpreting the data as Base64 encoded
	 */

	mInit((unsigned char *) data, &handle, length);
	got = Mread(header, 10, 1, &handle);
	if (got != 10 ||
		((strncmp(GIF87a, (char *) header, 6) != 0)
		&& (strncmp(GIF89a, (char *) header, 6) != 0))) {
	    return 0;
	}
    } else {
	memcpy(header, data, 10);
    }
    *widthPtr = LM_to_uint(header[6], header[7]);
    *heightPtr = LM_to_uint(header[8], header[9]);
    return 1;
}

/*
 *----------------------------------------------------------------------
 *
 * StringReadGIF --
 *
 *	This function is called by the photo image type to read GIF format
 *	data from an object, optionally base64 encoded, and give it to the
 *	photo image.
 *
 * Results:
 *	A standard TCL completion code. If TCL_ERROR is returned then an error
 *	message is left in the interp's result.
 *
 * Side effects:
 *	New data is added to the image given by imageHandle. This function
 *	calls FileReadGIF by redefining the operation of fprintf temporarily.
 *
 *----------------------------------------------------------------------
 */

static int
StringReadGIF(
    Tcl_Interp *interp,		/* interpreter for reporting errors in */
    Tcl_Obj *dataObj,		/* object containing the image */
    Tcl_Obj *format,		/* format object, or NULL */
    Tk_PhotoHandle imageHandle,	/* the image to write this data into */
    int destX, int destY,	/* The rectangular region of the */
    int width, int height,	/* image to copy */
    int srcX, int srcY)
{
    MFile handle, *hdlPtr = &handle;
    int length;
    const char *xferFormat;
    unsigned char *data = Tcl_GetByteArrayFromObj(dataObj, &length);

    mInit(data, hdlPtr, length);

    /*
     * Check whether the data is Base64 encoded by doing a character-by-
     * charcter comparison with the binary-format headers; BASE64-encoded
     * never matches (matching the other way is harder because of potential
     * padding of the BASE64 data).
     */

    if (strncmp(GIF87a, (char *) data, 6)
	    && strncmp(GIF89a, (char *) data, 6)) {
	xferFormat = INLINE_DATA_BASE64;
    } else {
	xferFormat = INLINE_DATA_BINARY;
    }

    /*
     * Fall through to the file reader now that we have a correctly-configured
     * pseudo-channel to pull the data from.
     */

    return FileReadGIF(interp, (Tcl_Channel) hdlPtr, xferFormat, format,
	    imageHandle, destX, destY, width, height, srcX, srcY);
}

/*
 *----------------------------------------------------------------------
 *
 * ReadGIFHeader --
 *
 *	This function reads the GIF header from the beginning of a GIF file
 *	and returns the dimensions of the image.
 *
 * Results:
 *	The return value is 1 if file "f" appears to start with a valid GIF
 *	header, 0 otherwise. If the header is valid, then *widthPtr and
 *	*heightPtr are modified to hold the dimensions of the image.
 *
 * Side effects:
 *	The access position in f advances.
 *
 *----------------------------------------------------------------------
 */

static int
ReadGIFHeader(
    GIFImageConfig *gifConfPtr,
    Tcl_Channel chan,		/* Image file to read the header from */
    int *widthPtr, int *heightPtr)
				/* The dimensions of the image are returned
				 * here. */
{
    unsigned char buf[7];

    if ((Fread(gifConfPtr, buf, 1, 6, chan) != 6)
	    || ((strncmp(GIF87a, (char *) buf, 6) != 0)
	    && (strncmp(GIF89a, (char *) buf, 6) != 0))) {
	return 0;
    }

    if (Fread(gifConfPtr, buf, 1, 4, chan) != 4) {
	return 0;
    }

    *widthPtr = LM_to_uint(buf[0], buf[1]);
    *heightPtr = LM_to_uint(buf[2], buf[3]);
    return 1;
}

/*
 *-----------------------------------------------------------------
 * The code below is copied from the giftoppm program and modified just
 * slightly.
 *-----------------------------------------------------------------
 */

static int
ReadColorMap(
    GIFImageConfig *gifConfPtr,
    Tcl_Channel chan,
    int number,
    unsigned char buffer[MAXCOLORMAPSIZE][4])
{
    int i;
    unsigned char rgb[3];

    for (i = 0; i < number; ++i) {
	if (Fread(gifConfPtr, rgb, sizeof(rgb), 1, chan) <= 0) {
	    return 0;
	}

	if (buffer) {
	    buffer[i][CM_RED] = rgb[0];
	    buffer[i][CM_GREEN] = rgb[1];
	    buffer[i][CM_BLUE] = rgb[2];
	    buffer[i][CM_ALPHA] = 255;
	}
    }
    return 1;
}

static int
DoExtension(
    GIFImageConfig *gifConfPtr,
    Tcl_Channel chan,
    int label,
    unsigned char *buf,
    int *transparent)
{
    int count;

    switch (label) {
    case 0x01:		/* Plain Text Extension */
	break;

    case 0xff:		/* Application Extension */
	break;

    case 0xfe:		/* Comment Extension */
	do {
	    count = GetDataBlock(gifConfPtr, chan, buf);
	} while (count > 0);
	return count;

    case 0xf9:		/* Graphic Control Extension */
	count = GetDataBlock(gifConfPtr, chan, buf);
	if (count < 0) {
	    return 1;
	}
	if ((buf[0] & 0x1) != 0) {
	    *transparent = buf[3];
	}

	do {
	    count = GetDataBlock(gifConfPtr, chan, buf);
	} while (count > 0);
	return count;
    }

    do {
	count = GetDataBlock(gifConfPtr, chan, buf);
    } while (count > 0);
    return count;
}

static int
GetDataBlock(
    GIFImageConfig *gifConfPtr,
    Tcl_Channel chan,
    unsigned char *buf)
{
    unsigned char count;

    if (Fread(gifConfPtr, &count, 1, 1, chan) <= 0) {
	return -1;
    }

    if ((count != 0) && (Fread(gifConfPtr, buf, count, 1, chan) <= 0)) {
	return -1;
    }

    return count;
}

/*
 *----------------------------------------------------------------------
 *
 * ReadImage --
 *
 *	Process a GIF image from a given source, with a given height, width,
 *	transparency, etc.
 *
 *	This code is based on the code found in the ImageMagick GIF decoder,
 *	which is (c) 2000 ImageMagick Studio.
 *
 *	Some thoughts on our implementation:
 *	It sure would be nice if ReadImage didn't take 11 parameters! I think
 *	that if we were smarter, we could avoid doing that.
 *
 *	Possible further optimizations: we could pull the GetCode function
 *	directly into ReadImage, which would improve our speed.
 *
 * Results:
 *	Processes a GIF image and loads the pixel data into a memory array.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
ReadImage(
    GIFImageConfig *gifConfPtr,
    Tcl_Interp *interp,
    unsigned char *imagePtr,
    Tcl_Channel chan,
    int len, int rows,
    unsigned char cmap[MAXCOLORMAPSIZE][4],
    int srcX, int srcY,
    int interlace,
    int transparent)
{
    unsigned char initialCodeSize;
    int xpos = 0, ypos = 0, pass = 0, i;
    register unsigned char *pixelPtr;
    static const int interlaceStep[] = { 8, 8, 4, 2 };
    static const int interlaceStart[] = { 0, 4, 2, 1 };
    unsigned short prefix[(1 << MAX_LWZ_BITS)];
    unsigned char append[(1 << MAX_LWZ_BITS)];
    unsigned char stack[(1 << MAX_LWZ_BITS)*2];
    register unsigned char *top;
    int codeSize, clearCode, inCode, endCode, oldCode, maxCode;
    int code, firstCode, v;

    /*
     * Initialize the decoder
     */

    if (Fread(gifConfPtr, &initialCodeSize, 1, 1, chan) <= 0) {
	Tcl_AppendResult(interp, "error reading GIF image: ",
		Tcl_PosixError(interp), NULL);
	return TCL_ERROR;
    }

    if (initialCodeSize > MAX_LWZ_BITS) {
	Tcl_SetResult(interp, "malformed image", TCL_STATIC);
	return TCL_ERROR;
    }

    if (transparent != -1) {
	cmap[transparent][CM_RED] = 0;
	cmap[transparent][CM_GREEN] = 0;
	cmap[transparent][CM_BLUE] = 0;
	cmap[transparent][CM_ALPHA] = 0;
    }

    pixelPtr = imagePtr;

    /*
     * Initialize the decoder.
     *
     * Set values for "special" numbers:
     * clear code	reset the decoder
     * end code		stop decoding
     * code size	size of the next code to retrieve
     * max code		next available table position
     */

    clearCode = 1 << (int) initialCodeSize;
    endCode = clearCode + 1;
    codeSize = (int) initialCodeSize + 1;
    maxCode = clearCode + 2;
    oldCode = -1;
    firstCode = -1;

    memset(prefix, 0, (1 << MAX_LWZ_BITS) * sizeof(short));
    memset(append, 0, (1 << MAX_LWZ_BITS) * sizeof(char));
    for (i = 0; i < clearCode; i++) {
	append[i] = i;
    }
    top = stack;

    GetCode(chan, 0, 1, gifConfPtr);

    /*
     * Read until we finish the image
     */

    for (i = 0, ypos = 0; i < rows; i++) {
	for (xpos = 0; xpos < len; ) {
	    if (top == stack) {
		/*
		 * Bummer - our stack is empty. Now we have to work!
		 */

		code = GetCode(chan, codeSize, 0, gifConfPtr);
		if (code < 0) {
		    return TCL_OK;
		}

		if (code > maxCode || code == endCode) {
		    /*
		     * If we're doing things right, we should never receive a
		     * code that is greater than our current maximum code. If
		     * we do, bail, because our decoder does not yet have that
		     * code set up.
		     *
		     * If the code is the magic endCode value, quit.
		     */

		    return TCL_OK;
		}

		if (code == clearCode) {
		    /*
		     * Reset the decoder.
		     */

		    codeSize = initialCodeSize + 1;
		    maxCode = clearCode + 2;
		    oldCode = -1;
		    continue;
		}

		if (oldCode == -1) {
		    /*
		     * Last pass reset the decoder, so the first code we see
		     * must be a singleton. Seed the stack with it, and set up
		     * the old/first code pointers for insertion into the
		     * string table. We can't just roll this into the
		     * clearCode test above, because at that point we have not
		     * yet read the next code.
		     */

		    *top++ = append[code];
		    oldCode = code;
		    firstCode = code;
		    continue;
		}

		inCode = code;

		if (code == maxCode) {
		    /*
		     * maxCode is always one bigger than our highest assigned
		     * code. If the code we see is equal to maxCode, then we
		     * are about to add a new string to the table. ???
		     */

		    *top++ = firstCode;
		    code = oldCode;
		}

		while (code > clearCode) {
		    /*
		     * Populate the stack by tracing the string in the string
		     * table from its tail to its head
		     */

		    *top++ = append[code];
		    code = prefix[code];
		}
		firstCode = append[code];

		/*
		 * If there's no more room in our string table, quit.
		 * Otherwise, add a new string to the table
		 */

		if (maxCode >= (1 << MAX_LWZ_BITS)) {
		    return TCL_OK;
		}

		/*
		 * Push the head of the string onto the stack.
		 */

		*top++ = firstCode;

		/*
		 * Add a new string to the string table
		 */

		prefix[maxCode] = oldCode;
		append[maxCode] = firstCode;
		maxCode++;

		/*
		 * maxCode tells us the maximum code value we can accept. If
		 * we see that we need more bits to represent it than we are
		 * requesting from the unpacker, we need to increase the
		 * number we ask for.
		 */

		if ((maxCode >= (1 << codeSize))
			&& (maxCode < (1<<MAX_LWZ_BITS))) {
		    codeSize++;
		}
		oldCode = inCode;
	    }

	    /*
	     * Pop the next color index off the stack.
	     */

	    v = *(--top);
	    if (v < 0) {
		return TCL_OK;
	    }

	    /*
	     * If pixelPtr is null, we're skipping this image (presumably
	     * there are more in the file and we will be called to read one of
	     * them later)
	     */

	    *pixelPtr++ = cmap[v][CM_RED];
	    *pixelPtr++ = cmap[v][CM_GREEN];
	    *pixelPtr++ = cmap[v][CM_BLUE];
	    if (transparent >= 0) {
		*pixelPtr++ = cmap[v][CM_ALPHA];
	    }
	    xpos++;

	}

	/*
	 * If interlacing, the next ypos is not just +1.
	 */

	if (interlace) {
	    ypos += interlaceStep[pass];
	    while (ypos >= rows) {
		pass++;
		if (pass > 3) {
		    return TCL_OK;
		}
		ypos = interlaceStart[pass];
	    }
	} else {
	    ypos++;
	}
	pixelPtr = imagePtr + (ypos) * len * ((transparent>=0)?4:3);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * GetCode --
 *
 *	Extract the next compression code from the file. In GIF's, the
 *	compression codes are between 3 and 12 bits long and are then packed
 *	into 8 bit bytes, left to right, for example:
 *		bbbaaaaa
 *		dcccccbb
 *		eeeedddd
 *		...
 *	We use a byte buffer read from the file and a sliding window to unpack
 *	the bytes. Thanks to ImageMagick for the sliding window idea.
 *	args:  chan	    the channel to read from
 *	       code_size    size of the code to extract
 *	       flag	    boolean indicating whether the extractor should be
 *			    reset or not
 *
 * Results:
 *	code		    the next compression code
 *
 * Side effects:
 *	May consume more input from chan.
 *
 *----------------------------------------------------------------------
 */

static int
GetCode(
    Tcl_Channel chan,
    int code_size,
    int flag,
    GIFImageConfig *gifConfPtr)
{
    int ret;

    if (flag) {
	/*
	 * Initialize the decoder.
	 */

	gifConfPtr->reader.bitsInWindow = 0;
	gifConfPtr->reader.bytes = 0;
	gifConfPtr->reader.window = 0;
	gifConfPtr->reader.done = 0;
	gifConfPtr->reader.c = NULL;
	return 0;
    }

    while (gifConfPtr->reader.bitsInWindow < code_size) {
	/*
	 * Not enough bits in our window to cover the request.
	 */

	if (gifConfPtr->reader.done) {
	    return -1;
	}
	if (gifConfPtr->reader.bytes == 0) {
	    /*
	     * Not enough bytes in our buffer to add to the window.
	     */

	    gifConfPtr->reader.bytes =
		    GetDataBlock(gifConfPtr, chan, gifConfPtr->workingBuffer);
	    gifConfPtr->reader.c = gifConfPtr->workingBuffer;
	    if (gifConfPtr->reader.bytes <= 0) {
		gifConfPtr->reader.done = 1;
		break;
	    }
	}

	/*
	 * Tack another byte onto the window, see if that's enough.
	 */

	gifConfPtr->reader.window +=
		(*gifConfPtr->reader.c) << gifConfPtr->reader.bitsInWindow;
	gifConfPtr->reader.c++;
	gifConfPtr->reader.bitsInWindow += 8;
	gifConfPtr->reader.bytes--;
    }

    /*
     * The next code will always be the last code_size bits of the window.
     */

    ret = gifConfPtr->reader.window & ((1 << code_size) - 1);

    /*
     * Shift data in the window to put the next code at the end.
     */

    gifConfPtr->reader.window >>= code_size;
    gifConfPtr->reader.bitsInWindow -= code_size;
    return ret;
}

/*
 *----------------------------------------------------------------------
 *
 * Minit -- --
 *
 *	This function initializes a base64 decoder handle
 *
 * Results:
 *	None
 *
 * Side effects:
 *	The base64 handle is initialized
 *
 *----------------------------------------------------------------------
 */

static void
mInit(
    unsigned char *string,	/* string containing initial mmencoded data */
    MFile *handle,		/* mmdecode "file" handle */
    int length)			/* Number of bytes in string */
{
    handle->data = string;
    handle->state = 0;
    handle->c = 0;
    handle->length = length;
}

/*
 *----------------------------------------------------------------------
 *
 * Mread --
 *
 *	This function is invoked by the GIF file reader as a temporary
 *	replacement for "fread", to get GIF data out of a string (using
 *	Mgetc).
 *
 * Results:
 *	The return value is the number of characters "read"
 *
 * Side effects:
 *	The base64 handle will change state.
 *
 *----------------------------------------------------------------------
 */

static int
Mread(
    unsigned char *dst,		/* where to put the result */
    size_t chunkSize,		/* size of each transfer */
    size_t numChunks,		/* number of chunks */
    MFile *handle)		/* mmdecode "file" handle */
{
    register int i, c;
    int count = chunkSize * numChunks;

    for (i=0; i<count && (c=Mgetc(handle)) != GIF_DONE; i++) {
	*dst++ = c;
    }
    return i;
}

/*
 *----------------------------------------------------------------------
 *
 * Mgetc --
 *
 *	This function gets the next decoded character from an mmencode handle.
 *	This causes at least 1 character to be "read" from the encoded string.
 *
 * Results:
 *	The next byte (or GIF_DONE) is returned.
 *
 * Side effects:
 *	The base64 handle will change state.
 *
 *----------------------------------------------------------------------
 */

static int
Mgetc(
    MFile *handle)		/* Handle containing decoder data and state */
{
    int c;
    int result = 0;		/* Initialization needed only to prevent gcc
				 * compiler warning. */

    if (handle->state == GIF_DONE) {
	return GIF_DONE;
    }

    do {
	if (handle->length-- <= 0) {
	    return GIF_DONE;
	}
	c = char64(*handle->data);
	handle->data++;
    } while (c == GIF_SPACE);

    if (c>GIF_SPECIAL) {
	handle->state = GIF_DONE;
	return handle->c;
    }

    switch (handle->state++) {
    case 0:
	handle->c = c<<2;
	result = Mgetc(handle);
	break;
    case 1:
	result = handle->c | (c>>4);
	handle->c = (c&0xF)<<4;
	break;
    case 2:
	result = handle->c | (c>>2);
	handle->c = (c&0x3) << 6;
	break;
    case 3:
	result = handle->c | c;
	handle->state = 0;
	break;
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * char64 --
 *
 *	This function converts a base64 ascii character into its binary
 *	equivalent. This code is a slightly modified version of the char64
 *	function in N. Borenstein's metamail decoder.
 *
 * Results:
 *	The binary value, or an error code.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
char64(
    int c)
{
    switch(c) {
    case 'A': return 0;  case 'B': return 1;  case 'C': return 2;
    case 'D': return 3;  case 'E': return 4;  case 'F': return 5;
    case 'G': return 6;  case 'H': return 7;  case 'I': return 8;
    case 'J': return 9;  case 'K': return 10; case 'L': return 11;
    case 'M': return 12; case 'N': return 13; case 'O': return 14;
    case 'P': return 15; case 'Q': return 16; case 'R': return 17;
    case 'S': return 18; case 'T': return 19; case 'U': return 20;
    case 'V': return 21; case 'W': return 22; case 'X': return 23;
    case 'Y': return 24; case 'Z': return 25; case 'a': return 26;
    case 'b': return 27; case 'c': return 28; case 'd': return 29;
    case 'e': return 30; case 'f': return 31; case 'g': return 32;
    case 'h': return 33; case 'i': return 34; case 'j': return 35;
    case 'k': return 36; case 'l': return 37; case 'm': return 38;
    case 'n': return 39; case 'o': return 40; case 'p': return 41;
    case 'q': return 42; case 'r': return 43; case 's': return 44;
    case 't': return 45; case 'u': return 46; case 'v': return 47;
    case 'w': return 48; case 'x': return 49; case 'y': return 50;
    case 'z': return 51; case '0': return 52; case '1': return 53;
    case '2': return 54; case '3': return 55; case '4': return 56;
    case '5': return 57; case '6': return 58; case '7': return 59;
    case '8': return 60; case '9': return 61; case '+': return 62;
    case '/': return 63;

    case ' ': case '\t': case '\n': case '\r': case '\f':
	return GIF_SPACE;
    case '=':
	return GIF_PAD;
    case '\0':
	return GIF_DONE;
    default:
	return GIF_BAD;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Fread --
 *
 *	This function calls either fread or Mread to read data from a file or
 *	a base64 encoded string.
 *
 * Results: - same as POSIX fread() or Tcl Tcl_Read()
 *
 *----------------------------------------------------------------------
 */

static int
Fread(
    GIFImageConfig *gifConfPtr,
    unsigned char *dst,		/* where to put the result */
    size_t hunk, size_t count,	/* how many */
    Tcl_Channel chan)
{
    if (gifConfPtr->fromData == INLINE_DATA_BASE64) {
	return Mread(dst, hunk, count, (MFile *) chan);
    }

    if (gifConfPtr->fromData == INLINE_DATA_BINARY) {
	MFile *handle = (MFile *) chan;

	if (handle->length <= 0 || (size_t) handle->length < hunk*count) {
	    return -1;
	}
	memcpy(dst, handle->data, (size_t) (hunk * count));
	handle->data += hunk * count;
	return (int)(hunk * count);
    }

    /*
     * Otherwise we've got a real file to read.
     */

    return Tcl_Read(chan, (char *) dst, (int) (hunk * count));
}

/*
 * ChanWriteGIF - writes a image in GIF format.
 *-------------------------------------------------------------------------
 * Author:		Lolo
 *			Engeneering Projects Area
 *			Department of Mining
 *			University of Oviedo
 * e-mail		zz11425958@zeus.etsimo.uniovi.es
 *			lolo@pcsig22.etsimo.uniovi.es
 * Date:		Fri September 20 1996
 *
 * Modified for transparency handling (gif89a) and miGIF compression
 * by Jan Nijtmans <j.nijtmans@chello.nl>
 *
 *----------------------------------------------------------------------
 * FileWriteGIF-
 *
 *	This function is called by the photo image type to write GIF format
 *	data from a photo image into a given file
 *
 * Results:
 *	A standard TCL completion code. If TCL_ERROR is returned then an error
 *	message is left in interp->result.
 *
 *----------------------------------------------------------------------
 */

/*
 * Types, defines and variables needed to write and compress a GIF.
 */

typedef int (* ifunptr) (ClientData clientData);

#define LSB(a)		((unsigned char) (((short)(a)) & 0x00FF))
#define MSB(a)		((unsigned char) (((short)(a)) >> 8))

#define GIFBITS		12
#define HSIZE		5003	/* 80% occupancy */

typedef struct {
    int ssize;
    int csize;
    int rsize;
    unsigned char *pixelo;
    int pixelSize;
    int pixelPitch;
    int greenOffset;
    int blueOffset;
    int alphaOffset;
    int num;
    unsigned char mapa[MAXCOLORMAPSIZE][3];
} GifWriterState;

/*
 * Definition of new functions to write GIFs
 */

static int		color(GifWriterState *statePtr,
			    int red, int green, int blue,
			    unsigned char mapa[MAXCOLORMAPSIZE][3]);
static void		compress(int initBits, Tcl_Channel handle,
			    ifunptr readValue, ClientData clientData);
static int		nuevo(GifWriterState *statePtr,
			    int red, int green, int blue,
			    unsigned char mapa[MAXCOLORMAPSIZE][3]);
static void		savemap(GifWriterState *statePtr,
			    Tk_PhotoImageBlock *blockPtr,
			    unsigned char mapa[MAXCOLORMAPSIZE][3]);
static int		ReadValue(ClientData clientData);

static int
FileWriteGIF(
    Tcl_Interp *interp,		/* Interpreter to use for reporting errors. */
    const char *filename,
    Tcl_Obj *format,
    Tk_PhotoImageBlock *blockPtr)
{
    Tcl_Channel chan = NULL;
    int result;

    chan = Tcl_OpenFileChannel(interp, (char *) filename, "w", 0644);
    if (!chan) {
	return TCL_ERROR;
    }
    if (Tcl_SetChannelOption(interp, chan, "-translation",
	    "binary") != TCL_OK) {
	Tcl_Close(NULL, chan);
	return TCL_ERROR;
    }

    result = CommonWriteGIF(interp, chan, format, blockPtr);

    if (Tcl_Close(interp, chan) == TCL_ERROR) {
	return TCL_ERROR;
    }
    return result;
}

static int
CommonWriteGIF(
    Tcl_Interp *interp,
    Tcl_Channel handle,
    Tcl_Obj *format,
    Tk_PhotoImageBlock *blockPtr)
{
    GifWriterState state, *statePtr = &state;
    int resolution;
    long width, height, x;
    unsigned char c;
    unsigned int top, left;

    top = 0;
    left = 0;

    memset(statePtr, 0, sizeof(state));

    statePtr->pixelSize = blockPtr->pixelSize;
    statePtr->greenOffset = blockPtr->offset[1]-blockPtr->offset[0];
    statePtr->blueOffset = blockPtr->offset[2]-blockPtr->offset[0];
    statePtr->alphaOffset = blockPtr->offset[0];
    if (statePtr->alphaOffset < blockPtr->offset[2]) {
	statePtr->alphaOffset = blockPtr->offset[2];
    }
    if (++statePtr->alphaOffset < statePtr->pixelSize) {
	statePtr->alphaOffset -= blockPtr->offset[0];
    } else {
	statePtr->alphaOffset = 0;
    }

    Tcl_Write(handle, (char *) (statePtr->alphaOffset ? GIF89a : GIF87a), 6);

    for (x=0 ; x<MAXCOLORMAPSIZE ; x++) {
	statePtr->mapa[x][CM_RED] = 255;
	statePtr->mapa[x][CM_GREEN] = 255;
	statePtr->mapa[x][CM_BLUE] = 255;
    }

    width = blockPtr->width;
    height = blockPtr->height;
    statePtr->pixelo = blockPtr->pixelPtr + blockPtr->offset[0];
    statePtr->pixelPitch = blockPtr->pitch;
    savemap(statePtr, blockPtr, statePtr->mapa);
    if (statePtr->num >= MAXCOLORMAPSIZE) {
	Tcl_AppendResult(interp, "too many colors", NULL);
	return TCL_ERROR;
    }
    if (statePtr->num<2) {
	statePtr->num = 2;
    }
    c = LSB(width);
    Tcl_Write(handle, (char *) &c, 1);
    c = MSB(width);
    Tcl_Write(handle, (char *) &c, 1);
    c = LSB(height);
    Tcl_Write(handle, (char *) &c, 1);
    c = MSB(height);
    Tcl_Write(handle, (char *) &c, 1);

    resolution = 0;
    while (statePtr->num >> resolution) {
	resolution++;
    }
    c = 111 + resolution * 17;
    Tcl_Write(handle, (char *) &c, 1);

    statePtr->num = 1 << resolution;

    /*
     * Background color
     */

    c = 0;
    Tcl_Write(handle, (char *) &c, 1);

    /*
     * Zero for future expansion.
     */

    Tcl_Write(handle, (char *) &c, 1);

    for (x=0 ; x<statePtr->num ; x++) {
	c = statePtr->mapa[x][CM_RED];
	Tcl_Write(handle, (char *) &c, 1);
	c = statePtr->mapa[x][CM_GREEN];
	Tcl_Write(handle, (char *) &c, 1);
	c = statePtr->mapa[x][CM_BLUE];
	Tcl_Write(handle, (char *) &c, 1);
    }

    /*
     * Write out extension for transparent colour index, if necessary.
     */

    if (statePtr->alphaOffset) {
	c = GIF_EXTENSION;
	Tcl_Write(handle, (char *) &c, 1);
	Tcl_Write(handle, "\371\4\1\0\0\0", 7);
    }

    c = GIF_START;
    Tcl_Write(handle, (char *) &c, 1);
    c = LSB(top);
    Tcl_Write(handle, (char *) &c, 1);
    c = MSB(top);
    Tcl_Write(handle, (char *) &c, 1);
    c = LSB(left);
    Tcl_Write(handle, (char *) &c, 1);
    c = MSB(left);
    Tcl_Write(handle, (char *) &c, 1);

    c = LSB(width);
    Tcl_Write(handle, (char *) &c, 1);
    c = MSB(width);
    Tcl_Write(handle, (char *) &c, 1);

    c = LSB(height);
    Tcl_Write(handle, (char *) &c, 1);
    c = MSB(height);
    Tcl_Write(handle, (char *) &c, 1);

    c = 0;
    Tcl_Write(handle, (char *) &c, 1);
    c = resolution;
    Tcl_Write(handle, (char *) &c, 1);

    statePtr->ssize = statePtr->rsize = blockPtr->width;
    statePtr->csize = blockPtr->height;
    compress(resolution+1, handle, ReadValue, (ClientData) statePtr);

    c = 0;
    Tcl_Write(handle, (char *) &c, 1);
    c = GIF_TERMINATOR;
    Tcl_Write(handle, (char *) &c, 1);

    return TCL_OK;
}

static int
color(
    GifWriterState *statePtr,
    int red, int green, int blue,
    unsigned char mapa[MAXCOLORMAPSIZE][3])
{
    int x = (statePtr->alphaOffset != 0);

    for (; x<=MAXCOLORMAPSIZE ; x++) {
	if ((mapa[x][CM_RED] == red) && (mapa[x][CM_GREEN] == green) &&
		(mapa[x][CM_BLUE] == blue)) {
	    return x;
	}
    }
    return -1;
}

static int
nuevo(
    GifWriterState *statePtr,
    int red, int green, int blue,
    unsigned char mapa[MAXCOLORMAPSIZE][3])
{
    int x = (statePtr->alphaOffset != 0);

    for (; x<=statePtr->num ; x++) {
	if ((mapa[x][CM_RED] == red) && (mapa[x][CM_GREEN] == green) &&
		(mapa[x][CM_BLUE] == blue)) {
	    return 0;
	}
    }
    return 1;
}

static void
savemap(
    GifWriterState *statePtr,
    Tk_PhotoImageBlock *blockPtr,
    unsigned char mapa[MAXCOLORMAPSIZE][3])
{
    unsigned char *colores;
    int x, y;
    unsigned char red, green, blue;

    if (statePtr->alphaOffset) {
	statePtr->num = 0;
	mapa[0][CM_RED] = 0xd9;
	mapa[0][CM_GREEN] = 0xd9;
	mapa[0][CM_BLUE] = 0xd9;
    } else {
	statePtr->num = -1;
    }

    for (y=0 ; y<blockPtr->height ; y++) {
	colores = blockPtr->pixelPtr + blockPtr->offset[0] + y*blockPtr->pitch;
	for (x=0 ; x<blockPtr->width ; x++) {
	    if (!statePtr->alphaOffset || colores[statePtr->alphaOffset]!=0) {
		red = colores[0];
		green = colores[statePtr->greenOffset];
		blue = colores[statePtr->blueOffset];
		if (nuevo(statePtr, red, green, blue, mapa)) {
		    statePtr->num++;
		    if (statePtr->num >= MAXCOLORMAPSIZE) {
			return;
		    }
		    mapa[statePtr->num][CM_RED] = red;
		    mapa[statePtr->num][CM_GREEN] = green;
		    mapa[statePtr->num][CM_BLUE] = blue;
		}
	    }
	    colores += statePtr->pixelSize;
	}
    }
}

static int
ReadValue(
    ClientData clientData)
{
    GifWriterState *statePtr = (GifWriterState *) clientData;
    unsigned int col;

    if (statePtr->csize == 0) {
	return EOF;
    }
    if (statePtr->alphaOffset && statePtr->pixelo[statePtr->alphaOffset]==0) {
	col = 0;
    } else {
	col = color(statePtr, statePtr->pixelo[0],
		statePtr->pixelo[statePtr->greenOffset],
		statePtr->pixelo[statePtr->blueOffset], statePtr->mapa);
    }
    statePtr->pixelo += statePtr->pixelSize;
    if (--statePtr->ssize <= 0) {
	statePtr->ssize = statePtr->rsize;
	statePtr->csize--;
	statePtr->pixelo += statePtr->pixelPitch
		- (statePtr->rsize * statePtr->pixelSize);
    }

    return col;
}

/*
 *-----------------------------------------------------------------------
 *
 * miGIF Compression - mouse and ivo's GIF-compatible compression
 *
 *		-run length encoding compression routines-
 *
 * Copyright (C) 1998 Hutchison Avenue Software Corporation
 *		 http://www.hasc.com
 *		 info@hasc.com
 *
 * Permission to use, copy, modify, and distribute this software and its
 * documentation for any purpose and without fee is hereby granted, provided
 * that the above copyright notice appear in all copies and that both that
 * copyright notice and this permission notice appear in supporting
 * documentation. This software is provided "AS IS." The Hutchison Avenue
 * Software Corporation disclaims all warranties, either express or implied,
 * including but not limited to implied warranties of merchantability and
 * fitness for a particular purpose, with respect to this code and
 * accompanying documentation.
 *
 * The miGIF compression routines do not, strictly speaking, generate files
 * conforming to the GIF spec, since the image data is not LZW-compressed
 * (this is the point: in order to avoid transgression of the Unisys patent on
 * the LZW algorithm.) However, miGIF generates data streams that any
 * reasonably sane LZW decompresser will decompress to what we want.
 *
 * miGIF compression uses run length encoding. It compresses horizontal runs
 * of pixels of the same color. This type of compression gives good results on
 * images with many runs, for example images with lines, text and solid shapes
 * on a solid-colored background. It gives little or no compression on images
 * with few runs, for example digital or scanned photos.
 *
 *				 der Mouse
 *			mouse@rodents.montreal.qc.ca
 *	      7D C8 61 52 5D E7 2D 39  4E F1 31 3E E8 B3 27 4B
 *
 *			       ivo@hasc.com
 *
 * The Graphics Interchange Format(c) is the Copyright property of CompuServe
 * Incorporated. GIF(sm) is a Service Mark property of CompuServe Incorporated.
 *
 *-----------------------------------------------------------------------
 */

typedef struct {
    int runlengthPixel;
    int runlengthBaseCode;
    int runlengthCount;
    int runlengthTablePixel;
    int runlengthTableMax;
    int justCleared;
    int outputBits;
    int outputBitsInit;
    int outputCount;
    int outputBump;
    int outputBumpInit;
    int outputClear;
    int outputClearInit;
    int maxOcodes;
    int codeClear;
    int codeEOF;
    unsigned int obuf;
    int obits;
    Tcl_Channel ofile;
    unsigned char oblock[256];
    int oblen;
} miGIFState_t;

/*
 * Used only when debugging GIF compression code
 */
/* #define MIGIF_DEBUGGING_ENVARS */

#ifdef MIGIF_DEBUGGING_ENVARS

/*
 * This debugging code is _absolutely_ not thread-safe. It's also not normally
 * enabled either.
 */

static int verboseSet = 0;
static int verbose;
#define MIGIF_VERBOSE		(verboseSet?verbose:setVerbose())
#define DEBUGMSG(printfArgs)	if (MIGIF_VERBOSE) { printf printfArgs; }

static int
setVerbose(void)
{
    verbose = !!getenv("MIGIF_VERBOSE");
    verboseSet = 1;
    return verbose;
}

static const char *
binformat(
    unsigned int v,
    int nbits)
{
    static char bufs[8][64];
    static int bhand = 0;
    unsigned int bit;
    int bno;
    char *bp;

    bhand--;
    if (bhand < 0) {
	bhand = (sizeof(bufs) / sizeof(bufs[0])) - 1;
    }
    bp = &bufs[bhand][0];
    for (bno=nbits-1,bit=((unsigned int)1)<<bno ; bno>=0 ; bno--,bit>>=1) {
	*bp++ = (v & bit) ? '1' : '0';
	if (((bno&3) == 0) && (bno != 0)) {
	    *bp++ = '.';
	}
    }
    *bp = '\0';
    return &bufs[bhand][0];
}
#else /* !MIGIF_DEBUGGING_ENVARS */
#define DEBUGMSG(printfArgs) /* do nothing */
#endif

static void
writeBlock(
    miGIFState_t *statePtr)
{
    unsigned char c;

#ifdef MIGIF_DEBUGGING_ENVARS
    if (MIGIF_VERBOSE) {
	int i;
	printf("writeBlock %d:", statePtr->oblen);
	for (i=0 ; i<statePtr->oblen ; i++) {
	    printf(" %02x", statePtr->oblock[i]);
	}
	printf("\n");
    }
#endif
    c = statePtr->oblen;
    Tcl_Write(statePtr->ofile, (char *) &c, 1);
    Tcl_Write(statePtr->ofile, (char *) &statePtr->oblock[0], statePtr->oblen);
    statePtr->oblen = 0;
}

static void
blockOut(
    miGIFState_t *statePtr,
    unsigned c)
{
    DEBUGMSG(("blockOut %s\n", binformat(c, 8)));
    statePtr->oblock[statePtr->oblen++] = (unsigned char) c;
    if (statePtr->oblen >= 255) {
	writeBlock(statePtr);
    }
}

static void
blockFlush(
    miGIFState_t *statePtr)
{
    DEBUGMSG(("blockFlush\n"));
    if (statePtr->oblen > 0) {
	writeBlock(statePtr);
    }
}

static void
output(
    miGIFState_t *statePtr,
    int val)
{
    DEBUGMSG(("output %s [%s %d %d]\n", binformat(val, statePtr->outputBits),
	    binformat(statePtr->obuf, statePtr->obits), statePtr->obits,
	    statePtr->outputBits));
    statePtr->obuf |= val << statePtr->obits;
    statePtr->obits += statePtr->outputBits;
    while (statePtr->obits >= 8) {
	blockOut(statePtr, statePtr->obuf & 0xff);
	statePtr->obuf >>= 8;
	statePtr->obits -= 8;
    }
    DEBUGMSG(("output leaving [%s %d]\n",
	    binformat(statePtr->obuf, statePtr->obits), statePtr->obits));
}

static void
outputFlush(
    miGIFState_t *statePtr)
{
    DEBUGMSG(("outputFlush\n"));
    if (statePtr->obits > 0) {
	blockOut(statePtr, statePtr->obuf);
    }
    blockFlush(statePtr);
}

static void
didClear(
    miGIFState_t *statePtr)
{
    DEBUGMSG(("didClear\n"));
    statePtr->outputBits = statePtr->outputBitsInit;
    statePtr->outputBump = statePtr->outputBumpInit;
    statePtr->outputClear = statePtr->outputClearInit;
    statePtr->outputCount = 0;
    statePtr->runlengthTableMax = 0;
    statePtr->justCleared = 1;
}

static void
outputPlain(
    miGIFState_t *statePtr,
    int c)
{
    DEBUGMSG(("outputPlain %s\n", binformat(c, statePtr->outputBits)));
    statePtr->justCleared = 0;
    output(statePtr, c);
    statePtr->outputCount++;
    if (statePtr->outputCount >= statePtr->outputBump) {
	statePtr->outputBits++;
	statePtr->outputBump += 1 << (statePtr->outputBits - 1);
    }
    if (statePtr->outputCount >= statePtr->outputClear) {
	output(statePtr, statePtr->codeClear);
	didClear(statePtr);
    }
}

static unsigned int
isqrt(
    unsigned int x)
{
    unsigned int r;
    unsigned int v;

    if (x < 2) {
	return x;
    }
    for (v=x,r=1 ; v ; v>>=2,r<<=1);
    while (1) {
	v = ((x / r) + r) / 2;
	if (v==r || v==r+1) {
	    return r;
	}
	r = v;
    }
}

static int
computeTriangleCount(
    unsigned int count,
    unsigned int nrepcodes)
{
    unsigned int perrep;
    unsigned int cost;

    cost = 0;
    perrep = (nrepcodes * (nrepcodes+1)) / 2;
    while (count >= perrep) {
	cost += nrepcodes;
	count -= perrep;
    }
    if (count > 0) {
	unsigned int n = isqrt(count);

	while (n*(n+1) >= 2*count) {
	    n--;
	}
	while (n*(n+1) < 2*count) {
	    n++;
	}
	cost += n;
    }
    return (int) cost + 1;
}

static void
maxOutputClear(
    miGIFState_t *statePtr)
{
    statePtr->outputClear = statePtr->maxOcodes;
}

static void
resetOutputClear(
    miGIFState_t *statePtr)
{
    statePtr->outputClear = statePtr->outputClearInit;
    if (statePtr->outputCount >= statePtr->outputClear) {
	output(statePtr, statePtr->codeClear);
	didClear(statePtr);
    }
}

static void
runlengthFlushFromClear(
    miGIFState_t *statePtr,
    int count)
{
    int n;

    DEBUGMSG(("runlengthFlushFromClear %d\n", count));
    maxOutputClear(statePtr);
    statePtr->runlengthTablePixel = statePtr->runlengthPixel;
    n = 1;
    while (count > 0) {
	if (n == 1) {
	    statePtr->runlengthTableMax = 1;
	    outputPlain(statePtr, statePtr->runlengthPixel);
	    count--;
	} else if (count >= n) {
	    statePtr->runlengthTableMax = n;
	    outputPlain(statePtr, statePtr->runlengthBaseCode+n-2);
	    count -= n;
	} else if (count == 1) {
	    statePtr->runlengthTableMax++;
	    outputPlain(statePtr, statePtr->runlengthPixel);
	    count = 0;
	} else {
	    statePtr->runlengthTableMax++;
	    outputPlain(statePtr, statePtr->runlengthBaseCode+count-2);
	    count = 0;
	}
	if (statePtr->outputCount == 0) {
	    n = 1;
	} else {
	    n++;
	}
    }
    resetOutputClear(statePtr);
    DEBUGMSG(("runlengthFlushFromClear leaving tableMax=%d\n",
	    statePtr->runlengthTableMax));
}

static void
runlengthFlushClearOrRep(
    miGIFState_t *statePtr,
    int count)
{
    int withclr;

    DEBUGMSG(("runlengthFlushClearOrRep %d\n", count));
    withclr = computeTriangleCount((unsigned) count,
	    (unsigned) statePtr->maxOcodes);
    if (withclr < count) {
	output(statePtr, statePtr->codeClear);
	didClear(statePtr);
	runlengthFlushFromClear(statePtr, count);
    } else {
	for (; count>0 ; count--) {
	    outputPlain(statePtr, statePtr->runlengthPixel);
	}
    }
}

static void
runlengthFlushWithTable(
    miGIFState_t *statePtr,
    int count)
{
    int repmax;
    int repleft;
    int leftover;

    DEBUGMSG(("runlengthFlushWithTable %d\n", count));
    repmax = count / statePtr->runlengthTableMax;
    leftover = count % statePtr->runlengthTableMax;
    repleft = (leftover ? 1 : 0);
    if (statePtr->outputCount+repmax+repleft > statePtr->maxOcodes) {
	repmax = statePtr->maxOcodes - statePtr->outputCount;
	leftover = count - (repmax * statePtr->runlengthTableMax);
	repleft = computeTriangleCount((unsigned) leftover,
		(unsigned) statePtr->maxOcodes);
    }
    DEBUGMSG(("runlengthFlushWithTable repmax=%d leftover=%d repleft=%d\n",
	    repmax, leftover, repleft));
    if (computeTriangleCount((unsigned) count, (unsigned) statePtr->maxOcodes)
	    < repmax+repleft) {
	output(statePtr, statePtr->codeClear);
	didClear(statePtr);
	runlengthFlushFromClear(statePtr, count);
	return;
    }
    maxOutputClear(statePtr);
    for (; repmax>0 ; repmax--) {
	outputPlain(statePtr,
		statePtr->runlengthBaseCode + statePtr->runlengthTableMax - 2);
    }
    if (leftover) {
	if (statePtr->justCleared) {
	    runlengthFlushFromClear(statePtr, leftover);
	} else if (leftover == 1) {
	    outputPlain(statePtr, statePtr->runlengthPixel);
	} else {
	    outputPlain(statePtr, statePtr->runlengthBaseCode + leftover - 2);
	}
    }
    resetOutputClear(statePtr);
}

static void
runlengthFlush(
    miGIFState_t *statePtr)
{
    DEBUGMSG(("runlengthFlush [ %d %d\n", statePtr->runlengthCount,
	    statePtr->runlengthPixel));
    if (statePtr->runlengthCount == 1) {
	outputPlain(statePtr, statePtr->runlengthPixel);
	statePtr->runlengthCount = 0;
	DEBUGMSG(("runlengthFlush ]\n"));
	return;
    }
    if (statePtr->justCleared) {
	runlengthFlushFromClear(statePtr, statePtr->runlengthCount);
    } else if ((statePtr->runlengthTableMax < 2)
	    || (statePtr->runlengthTablePixel != statePtr->runlengthPixel)) {
	runlengthFlushClearOrRep(statePtr, statePtr->runlengthCount);
    } else {
	runlengthFlushWithTable(statePtr, statePtr->runlengthCount);
    }
    DEBUGMSG(("runlengthFlush ]\n"));
    statePtr->runlengthCount = 0;
}

static void
compress(
    int initBits,
    Tcl_Channel handle,
    ifunptr readValue,
    ClientData clientData)
{
    int c;
    miGIFState_t state, *statePtr = &state;

    memset(statePtr, 0, sizeof(state));

    statePtr->ofile = handle;
    statePtr->obuf = 0;
    statePtr->obits = 0;
    statePtr->oblen = 0;
    statePtr->codeClear = 1 << (initBits - 1);
    statePtr->codeEOF = statePtr->codeClear + 1;
    statePtr->runlengthBaseCode = statePtr->codeEOF + 1;
    statePtr->outputBumpInit = (1 << (initBits - 1)) - 1;

    /*
     * For images with a lot of runs, making outputClearInit larger will give
     * better compression.
     */

    statePtr->outputClearInit =
	    (initBits <= 3) ? 9 : (statePtr->outputBumpInit-1);
#ifdef MIGIF_DEBUGGING_ENVARS
    {
	const char *ocienv = getenv("MIGIF_OUT_CLEAR_INIT");

	if (ocienv) {
	    statePtr->outputClearInit = atoi(ocienv);
	    DEBUGMSG(("[overriding outputClearInit to %d]\n",
		    statePtr->outputClearInit));
	}
    }
#endif
    statePtr->outputBitsInit = initBits;
    statePtr->maxOcodes =
	    (1 << GIFBITS) - ((1 << (statePtr->outputBitsInit - 1)) + 3);
    didClear(statePtr);
    output(statePtr, statePtr->codeClear);
    statePtr->runlengthCount = 0;
    while (1) {
	c = readValue(clientData);
	if (statePtr->runlengthCount>0 && statePtr->runlengthPixel!=c) {
	    runlengthFlush(statePtr);
	}
	if (c == EOF) {
	    break;
	}
	if (statePtr->runlengthPixel == c) {
	    statePtr->runlengthCount++;
	} else {
	    statePtr->runlengthPixel = c;
	    statePtr->runlengthCount = 1;
	}
    }
    output(statePtr, statePtr->codeEOF);
    outputFlush(statePtr);
}

/*
 *-----------------------------------------------------------------------
 *
 * End of miGIF section - See copyright notice at start of section.
 *
 *-----------------------------------------------------------------------
 */

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
