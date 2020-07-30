import Connectable::*;
import External_Interfaces::*;
import SRAM_Interfaces::*;
import SRAM_Fake::*;
import Cache_Controller::*;

(* synthesize *)
module cache(IFC_Cache);
    IFC_Cache_Controller controller <- cache_controller();
    IFC_SRAM_Server#(Indx, Line) cache_way0 <- mkSRAM(511);
    IFC_SRAM_Server#(Indx, Line) cache_way1 <- mkSRAM(511);
    IFC_SRAM_Server#(Indx, Cache_Tag#(Tag)) cache_tag <- mkSRAM(511);
    mkConnection(controller.cache_way0, cache_way0);
    mkConnection(controller.cache_way1, cache_way1);
    mkConnection(controller.cache_tag, cache_tag);
    interface IFC_Cache_Processor proc = controller.proc;
    interface IFC_Cache_Processor mem = controller.mem;
endmodule: cache

