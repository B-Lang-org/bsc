
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

static FILE *infile_p = NULL;
static FILE *outfile_p = NULL;

// function ActionValue#(int) open (String filename)
// returns 0 if OK, 1 if error
int openreadfile (const char *filename)
{
  infile_p = fopen(filename, "r");
  if (infile_p == 0) {
    perror("Could not open file");
    exit(1);
  }
  return 0;
}

// function ActionValue#(int) open (String filename)
// returns 0 if OK, 1 if error
int openwritefile (const char *filename)
{
  outfile_p = fopen(filename, "w");
  if (outfile_p == 0) {
    perror("Could not open file");
    exit(1);
  }
  return 0;
}

// function ActionValue#(int) open (String filename)
// returns 0 if OK, 1 if error
int openappendfile (const char *filename)
{
  outfile_p = fopen(filename, "a");
  if (outfile_p == 0) {
    perror("Could not open file");
    exit(1);
  }
  return 0;
}


// Bluespec function ActionValue#(Maybe#(FixedPoint#(i,f)) readFixedPointif();
// Bluespec function ActionValue#(Bit#(32)) readFixedPointif(i,f);
// provisos --  isize + fsize <= 31
// out-of-bound is truncated to maxBound or minBound
// End of file return Invalid
unsigned int readFixedPoint_i_f (unsigned int isize, unsigned int fsize)
{
  static int eofReached = 0;
  if (eofReached) return 0;

  if (infile_p == NULL) {
    fprintf(stderr,"input file is not open\n");
    return 0;
  }

  double din;
  int stat = fscanf (infile_p, "%lg", &din );
  if (stat == EOF) {
    fprintf(stderr, "End of File reached in scanning Fixedpoint\n");
    eofReached = 1 ;
    return 0;
  }
  double maxBound = pow ((double) 2.0, (isize-1)) - (1.0/ pow ((double)2.0, fsize));
  double minBound = - pow ((double) 2.0, (double) (isize-1));
  if (din > maxBound) {
    fprintf(stderr, "Error: overflow converting %g to FixedPoint#(%d.%d), maxBound, %g, used\n", din, isize, fsize, maxBound);
    unsigned int ret = ~( (0x01) << (isize + fsize -1))  ;
    return ret;
  }
  if (din < minBound) {
    fprintf(stderr, "Error: underflow converting %g to FixedPoint#(%d.%d), minBound, %g, used\n", din, isize, fsize, minBound);
    unsigned int ret = ( (0x03) << (isize + fsize -1))  ;
    return ret;
  }
  int negative = din < 0.0;
  if (negative) din = - din;

  unsigned int intpart = (int) din;
  double fracpart = din - intpart;
  fracpart = fracpart * (2 << (fsize-1));
  unsigned int fracbit = (int) fracpart;
  int bits = fracbit | (intpart << fsize);
  if (negative) bits = - bits;
  bits |= 0x80000000 ;
  //printf ("Converted %f  to %08x  (%04x.%04x)\n",  din, bits, intpart, fracbit);
  return (unsigned int) bits;
}

void writeFixedPoint_i_f (unsigned int isize, unsigned int fsize, unsigned int din)
{
  if (outfile_p != NULL) {
    int dini = (int) din;
    double dind = (double) dini / (pow ((double)2.0, fsize));
    fprintf (outfile_p, "%8.6f", dind);
  }
  else {
    fprintf(stderr,"output file is not open\n");
  }
}

void writeString (const char * str)
{
  if (outfile_p != NULL) {
    fprintf (outfile_p, "%s", str); 
  }
  else {
    fprintf(stderr,"output file is not open\n");
  }
}

void writeNewLine ()
{
  if (outfile_p != NULL) {
    fprintf (outfile_p, "\n");
  }
  else {
    fprintf(stderr,"output file is not open\n");
  }
}
