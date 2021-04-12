interface M;
   method bit m(bit arg);
endinterface

import "BVI" TheM =
   module vM(M);
     no_reset;
     method OUT m(IN);
   endmodule
