#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>

/* ----------------------------------------------------------------
 */

char helpText[] =
   "This program takes an input file, usually a LaTeX source, in which\n"
   "a grammar has been described using the following macros\n"
   "    \\gram{}, \\grammore{} and \\gramalt{}\n"
   "and\n"
   "- extracts the \\gram{}, \\grammore{} and \\gramalt{} sections to one file\n"
   "- extracts the non-terminals to a second file, with counts on how many\n"
   "      times each non-terminal has been defined and used\n"
   "- extracts a sorted list of keywords to a third file\n"
   "\n"
   "Notes:\n"
   "  The \\gram... sections in the source must begin in column 1.\n"
   "  After a \\gram... line, each succeeding line that is non-empty\n"
   "      and begins with a space or tab is assumed to be a continuation\n"
   "      of the section\n"
   "  In each \\gram{foo}, foo is a non-terminal,\n"
   "      and this is a definition of foo\n"
   "  Within each section, for each \\nterm{foo}, foo is a non-terminal and\n"
   "      and this is a use of foo\n"
   "  Within each section, for each \\term{foo} where foo begins with a\n"
   "      lower-case alphabetic character, foo is a keyword\n";

/* ----------------------------------------------------------------
 * Output filenames
 */

char  outputFilename[]   = "rawbnf.tex";
char  nonTermsFilename[] = "non_terminals.txt";
char  kwFilename[]       = "keywords.tex";

/* ----------------------------------------------------------------
 * Standard defs
 */

typedef enum { FALSE, TRUE } Bool;

/* ----------------------------------------------------------------
 * Tables for non-terminals and keywords
 */

#define MAXTABLE  4096
#define WORDMAX     32

typedef char Word [WORDMAX];

typedef enum { GRAM_NOT_SEEN, GRAM_SEEN } NTermStatus;

typedef struct {
    Word  nterm;
    int   gramCount;
    int   ntermCount;
} NTermEntry;

NTermEntry  ntermTable [MAXTABLE];
int  numNTerms = 0;

Word kwordTable [MAXTABLE];
int  numKWords = 0;

/* ----------------------------------------------------------------
 * compareKWords()
 * Compares two keywords, for sorting purposes
 *
 * Converts each 'endfoo' keyword into 'foo ', for sorting purposes,
 * so that it will show up directly after the corresponding 'foo' keyword.
 * But note: 'end' itself should be left untouched
 */

int
compareKWords (const void *vp1, const void *vp2)
{
    Word   tmp1,  tmp2;
    const
    char  *kw1,  *kw2;

    kw1 = vp1;
    kw2 = vp2;

    if ((strlen (kw1) > 3) &&
	(strncmp (kw1, "end", 3) == 0)) {
	strcpy (tmp1, & (kw1[3]));
	strcat (tmp1, " ");
    }
    else
	strcpy (tmp1, kw1);

    if ((strlen (kw2) > 3) &&
	(strncmp (kw2, "end", 3) == 0)) {
	strcpy (tmp2, & (kw2[3]));
	strcat (tmp2, " ");
    }
    else
	strcpy (tmp2, kw2);

    return strcmp (tmp1, tmp2);
} /* compareKWords() */

/* ----------------------------------------------------------------
 * addKWord()
 * Registers a new non-terminal
 */

void
addKWord (char *kword)
{
    int j;

    // ---- Check if already exists
    for (j = 0; j < numKWords; j++) {
	if (strcmp (kword, kwordTable[j]) == 0) {
	    return;
	}
    }

    // --- If fell through to here, seeing it for first time
    if (numKWords == MAXTABLE) {
	fprintf (stderr, "Exceeded keyword table capacity (%d)\n", MAXTABLE);
	exit (1);
    }

    strcpy (kwordTable [numKWords], kword);
    numKWords++;
} /* addKWord() */

/* ----------------------------------------------------------------
 * addNTerm()
 * Registers a new non-terminal
 */

void
addNTerm (char *nterm, Bool inGram)
{
    int j;

    // ---- Check if already exists
    for (j = 0; j < numNTerms; j++) {
	if (strcmp (nterm, ntermTable[j].nterm) == 0) {
	    if (inGram)
		ntermTable [j].gramCount++;
	    else
		ntermTable [j].ntermCount++;
	    return;
	}
    }

    // --- If fell through to here, seeing it for first time
    if (numNTerms == MAXTABLE) {
	fprintf (stderr, "Exceeded nterm table capacity (%d)\n", MAXTABLE);
	exit (1);
    }

    strcpy (ntermTable [numNTerms].nterm, nterm);
    if (inGram) {
	ntermTable [j].gramCount = 1;
	ntermTable [j].ntermCount = 0;
    }
    else {
	ntermTable [j].gramCount = 0;
	ntermTable [j].ntermCount = 1;
    }
    numNTerms++;
} /* addNTerm() */

/* ----------------------------------------------------------------
 * processOutputLine()
 * Prints the line after trimming any trailing '\\'
 */

void
processOutputLine (FILE *fpo, char *inputLine)
{
    int   j, j1;
    Word  word;

    // j1 finds the last occurrence of \\, if any
    j1 = 0;
    for (j = 0; inputLine[j] != 0; j++) {
	if ((inputLine[j]   == '\\') &&
	    (inputLine[j+1] == '\\')) {
	    j1 = j;
	}
    }

    // if found, truncate the string there, with \n
    if (j1 != 0) {
	inputLine [j1] = '\n';
	inputLine [j1+1] = 0;
    }

    fprintf (fpo, "%s", inputLine);

    // ---- Register non-terminals from \gram lines
    if (strncmp (inputLine, "\\gram{", strlen ("\\gram{")) == 0) {
	for (j = 0; inputLine[j+6] != '}'; j++)
	    word [j] = inputLine[j+6];
	word [j] = 0;
	addNTerm (word, TRUE);
    }

    // ---- Register non-terminals from \nterm{} phrases
    for (j = 0; j < (strlen (inputLine) - 7); j++) {
	if (strncmp (& (inputLine[j]), "\\nterm{", strlen ("\\nterm{")) == 0) {
	    for (j1 = 0; inputLine[j+j1+7] != '}'; j1++)
		word [j1] = inputLine[j+j1+7];
	    word [j1] = 0;
	    addNTerm (word, FALSE);
	}
    }

    // ---- Register keywords from \term{} phrases
    for (j = 0; j < (strlen (inputLine) - 6); j++) {
	if ((strncmp (& (inputLine[j]), "\\term{", strlen ("\\term{")) == 0) &&
	    (isalpha (inputLine [j+6]))) {
	    for (j1 = 0; inputLine[j+j1+6] != '}'; j1++)
		word [j1] = inputLine[j+j1+6];
	    word [j1] = 0;
	    addKWord (word);
	}
    }
} /* processOutputLine() */

/* ----------------------------------------------------------------
 * processFile()
 */

#define LINEMAX 4096

char inputLine [LINEMAX];

void
processFile (FILE *fpi, FILE *fpo)
{
    char *cp;

    cp = fgets (inputLine, LINEMAX, fpi);
    while (1) {
	if (cp == NULL) break;

	if (strncmp (inputLine, "\\gram", strlen("\\gram")) != 0) {
	    // ordinary line; discard it
	    cp = fgets (inputLine, LINEMAX, fpi);
	    continue;
	}

	// Found a \gram, \grammore or \gramalt line
	processOutputLine (fpo, inputLine);

	// Print continuation lines if any: non-empty lines where
	// first char is whitespace
	cp = fgets (inputLine, LINEMAX, fpi);
	while (1) {
	    if (cp == NULL) break;
	    if ((inputLine[0] == ' ') ||
		(inputLine[0] == '\t'))
		processOutputLine (fpo, inputLine);
	    else
		break;
	    cp = fgets (inputLine, LINEMAX, fpi);
	}

	// Print a blank line, just for readability
	fprintf (fpo, "\n");
    }
} /* processFile() */

/* ----------------------------------------------------------------
 * printUsage()
 */

void
printUsage (FILE *fp, int argc, char *argv[])
{
    fprintf (fp, "Usage:    %s  inputfile\n", argv[0]);
    fprintf (fp, "          %s  ?/-h/-help    for more help\n", argv[0]);
    fprintf (fp, "Input file is typically a .tex file\n");
    fprintf (fp, "Extracts the \\gram{}, \\grammore{} and \\gramalt{} sections to file: %s\n",
	     outputFilename);
    fprintf (fp, "Prints non-terminals to file: %s\n", nonTermsFilename);
    fprintf (fp, "    along with # defs and # uses statistics for each non-terminal\n");
    fprintf (fp, "Prints sorted list of keywords to file: %s\n", nonTermsFilename);
} /* printUsage() */

/* ----------------------------------------------------------------
 * main()
 */

int
main (int argc, char *argv[])
{
    FILE  *fpi, *fpo, *fpnt, *fpkw;
    int   j, k;

    if ((argc == 2) &&
	((strcmp (argv[1], "?") == 0) ||
	 (strcmp (argv[1], "-h") == 0) ||
	 (strcmp (argv[1], "-help") == 0))) {
	printUsage (stdout, argc, argv);
	printf ("\n");
	printf ("%s", helpText);
	return 0;
    }

    if (argc != 2) {
	printUsage (stderr, argc, argv);
	return 1;
    }

    fpi = fopen (argv[1], "r");
    if (fpi == NULL) {
	fprintf (stderr, "Unable to open input file: %s\n", argv[1]);
	printUsage (stderr, argc, argv);
	return 1;
    }

    // ---- Process input file and write out grammar file
    fpo = fopen (outputFilename, "w");
    if (fpo == NULL) {
	fprintf (stderr, "Unable to open output file: %s\n", outputFilename);
	printUsage (stderr, argc, argv);
	return 1;
    }
    printf ("Writing grammar to file: %s\n", outputFilename);

    processFile (fpi, fpo);

    // ---- print nterm table
    fpnt = fopen (nonTermsFilename, "w");
    if (fpnt == NULL) {
	fprintf (stderr, "Unable to open output file for non-terminals: %s\n",
		 nonTermsFilename);
	printUsage (stderr, argc, argv);
	return 1;
    }
    printf ("Writing sorted keyword list to file: %s\n", nonTermsFilename);

    fprintf (fpnt, "Defs    Uses    Non-terminal\n");
    for (j = 0; j < numNTerms; j++) {
	fprintf (fpnt, "%4d    %4d    %s",
		 ntermTable[j].gramCount,
		 ntermTable[j].ntermCount,
		 ntermTable[j].nterm);
	if (ntermTable[j].gramCount < 1)
	    fprintf (fpnt, "  (no defs)");
	else if (ntermTable[j].gramCount > 1)
	    fprintf (fpnt, "  (multiple defs)");
	if (ntermTable[j].ntermCount == 0)
	    fprintf (fpnt, "  (no uses)");
	fprintf (fpnt, "\n");
    }

    // ---- sort and print keyword table
    fpkw = fopen (kwFilename, "w");
    if (fpkw == NULL) {
	fprintf (stderr, "Unable to open output file for keywords: %s\n", kwFilename);
	printUsage (stderr, argc, argv);
	return 1;
    }
    printf ("Writing sorted keyword list to file: %s\n", kwFilename);

    qsort (kwordTable, numKWords, sizeof (Word), compareKWords);

    fprintf (fpkw, "\\begin{verbatim}\n");
    for (j = 0; j < numKWords; j++) {
	if ((j < (numKWords - 1)) &&
	    (strncmp (kwordTable[j+1], "end", 3) == 0) &&
	    (strcmp  (kwordTable[j], kwordTable[j+1]+3) == 0)) {
	    fprintf (fpkw, "  %s", kwordTable[j]);
	    for (k = strlen (kwordTable[j]); k < WORDMAX; k++)
		fputc (' ', fpkw);
	    fprintf (fpkw, "  %s\n", kwordTable[j+1]);
	    j++;
	}
	else {
	    fprintf (fpkw, "  %s\n", kwordTable[j]);
	}
    }
    fprintf (fpkw, "\\end{verbatim}\n");

    return 0;
}
