// Provide an implementation for the Randomizable library's BDPI
// that's available without the user having to manually include it.
// XXX This should go away and be replaced with a mechanism in BSC
// XXX to auto-include such files from the Libraries

extern "C" unsigned int rand32 ();
