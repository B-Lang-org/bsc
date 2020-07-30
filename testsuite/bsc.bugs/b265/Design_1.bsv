package Design_1;
import  Design_0::*;

interface Design_IFC; 
    method Action start(
                        Bit#(1) bus_reqA,
                        Bit#(1) bus_reqB,
                        Bit#(1) bus_reqC,
                        Bit#(1) h_mbA,
                        Bit#(1) h_mbB,
                        Bit#(1) h_mbC,
                        Bit#(1) r_wbA,
                        Bit#(1) r_wbB,
                        Bit#(1) r_wbC
                       );
    method StateType  cont_stateA(); 
    method StateType  cont_stateB(); 
    method StateType  cont_stateC(); 
endinterface:  Design_IFC

(* synthesize *)
module mkDesign (Design_IFC);

    Reg#(Bit#(1)) bus_ackA();
    mkReg#(0) the_bus_ackA(bus_ackA);

    Reg#(Bit#(1)) bus_ackB();
    mkReg#(0) the_bus_ackB(bus_ackB);

    Reg#(Bit#(1)) bus_ackC();
    mkReg#(0) the_bus_ackC(bus_ackC);

    Reg#(Bit#(1)) h_mbA_reg ();
    mkReg#(0) the_h_mbA_reg(h_mbA_reg);

    Reg#(Bit#(1)) h_mbB_reg ();
    mkReg#(0) the_h_mbB_reg(h_mbB_reg);

    Reg#(Bit#(1)) h_mbC_reg ();
    mkReg#(0) the_h_mbC_reg(h_mbC_reg);
             
    Reg#(Bit#(1))  r_wbA_reg  ();
    mkReg#(0) the_r_wbA_reg ( r_wbA_reg );

    Reg#(Bit#(1))  r_wbB_reg  ();
    mkReg#(0) the_r_wbB_reg ( r_wbB_reg );

    Reg#(Bit#(1))  r_wbC_reg  ();
    mkReg#(0) the_r_wbC_reg ( r_wbC_reg );
    
    Reg#(Bit#(1)) info_availA  ();
    mkReg#(0) the_info_availA (info_availA  );

    Reg#(Bit#(1)) info_availB  ();
    mkReg#(0) the_info_availB (info_availB  );

    Reg#(Bit#(1)) info_availC  ();
    mkReg#(0) the_info_availC(info_availC);


    Design_in_IFC cacheA();
    mkDesign_in the_cacheA (cacheA);

    Design_in_IFC cacheB();
    mkDesign_in the_cacheB (cacheB);

    Design_in_IFC cacheC();
    mkDesign_in the_cacheC (cacheC);
            
    method Action start(
                        Bit#(1) bus_reqA,
                        Bit#(1) bus_reqB,
                        Bit#(1) bus_reqC,
                        Bit#(1) h_mbA,
                        Bit#(1) h_mbB,
                        Bit#(1) h_mbC,
                        Bit#(1) r_wbA,
                        Bit#(1) r_wbB,
                        Bit#(1) r_wbC
                       );

        action
            Bit#(1)     all_shared;
            Bit#(1)     is_snoop;
            Bit#(1)     invalidate;
            Bit#(1)     mem_served;
            SnoopType   snoop_type;   

            if (bus_reqA==1) bus_ackA <= 1; else bus_ackA <=  0;

            if (bus_reqB==1 && bus_reqA==0) bus_ackB <= 1; else bus_ackB <=  0;

            if (bus_reqC==1 && bus_reqA==0 && bus_reqB==0) bus_ackC <=  1; else bus_ackC <=  0;

            if (bus_reqA==1) h_mbA_reg <=  h_mbA; else h_mbA_reg <= 0;

            if (bus_reqB==1 && bus_reqA==0) h_mbB_reg <=  h_mbB; else h_mbB_reg <=  0;

            if (bus_reqC==1 && bus_reqA==0 && bus_reqB==0) h_mbC_reg  <=  h_mbC; else h_mbC_reg <=   0;

            if (bus_reqA==1) r_wbA_reg <=  r_wbA ; else r_wbA_reg <=  0;

            if (bus_reqB==1 && bus_reqA==0) r_wbB_reg <=  r_wbB; else r_wbB_reg <= 0;

            if (bus_reqC==1 && bus_reqA==0 && bus_reqB==0) r_wbC_reg <=  r_wbC; else r_wbC_reg <= 0;

            if (h_mbA==1) info_availA <=  1; else info_availA  <= 0;

            if (h_mbB==1) info_availB <=  1; else info_availB <= 0;

            if (h_mbC==1) info_availC <=  1; else info_availC <= 0;

            if (cacheA.is_shared==1 && cacheB.is_shared==1 && cacheC.is_shared==1) 
                all_shared =  1; 
            else 
                all_shared = 0 ;

            if (bus_ackA==1 || bus_ackB==1 || bus_ackC == 1) 
                is_snoop =   1; 
            else 
                is_snoop = 0;

            if (((bus_ackA==1) && (r_wbA_reg==0)) || 
                ((bus_ackB==1) && (r_wbB_reg==0)) || 
                ((bus_ackC==1) && (r_wbC_reg==0))) 
                invalidate =  1; 
            else 
                invalidate =  0;
                         
            if (((bus_ackA==1 && h_mbA_reg==0 && (info_availB==0 && info_availC==0)) ||
                 (bus_ackB==1 && h_mbB_reg==0 && (info_availC==0 && info_availA==0)) || 
                 (bus_ackC==1 && h_mbC_reg==0 && (info_availA==0 && info_availB==0)))) 
                mem_served = 1; 
            else 
                mem_served = 0;
 
            if (bus_ackA==1) 
                snoop_type =   cacheA.snoop_type_out(h_mbA_reg, r_wbA_reg);
            else if (bus_ackB==1) 
                snoop_type =   cacheB.snoop_type_out(h_mbB_reg,r_wbB_reg);
            else 
                snoop_type = cacheC.snoop_type_out(h_mbC_reg, r_wbC_reg);
                    
                     
            cacheA.start(r_wbA_reg, snoop_type, is_snoop, info_availA, invalidate, all_shared, mem_served, bus_ackA); 
            cacheB.start(r_wbB_reg, snoop_type, is_snoop, info_availB, invalidate, all_shared, mem_served, bus_ackB); 
            cacheC.start(r_wbC_reg, snoop_type, is_snoop, info_availC, invalidate, all_shared, mem_served, bus_ackC); 
        endaction
    endmethod: start

    method StateType cont_stateA (); 
        cont_stateA = cacheA.cont_state;
    endmethod:   cont_stateA

    method StateType cont_stateB (); 
        cont_stateB = cacheB.cont_state;
    endmethod:   cont_stateB

    method StateType cont_stateC (); 
        cont_stateC = cacheC.cont_state;
    endmethod:   cont_stateC

endmodule: mkDesign

endpackage: Design_1
