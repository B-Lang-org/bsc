typedef struct {
       CAM_repl_t repl;
       int addr;
} CAM_repl_t deriving (Bits, Eq);
// deriving Bits on recursive type fails
