package require InstSynth
namespace import ::InstSynth::*

genTypeClass FIFO { mkFIFO mkSizedFIFO }

genSpecificInst FIFO mkFIFO { FIFO#(int) } ;

## types with 2 arguments 
genTypeClass FIFOLevel { mkFIFOCount }

genSpecificInst FIFOLevel mkFIFOCount { {FIFOCountIfc#(int, 10)} } ;
genSpecificInst FIFOLevel mkFIFOCount { {FIFOCountIfc#( int, 11)} } ;


#######

