   // ----------------------------------------------------------------
interface Master_ifc#(type addr_type, type data_type, type resp_type, type status_type);
   // Master Interface

   // Arbiter reads request from master
   method Action master(data_type hrdata, Bool hgrant, Bit#(2) hresp);
   method data_type hwdata();
   method addr_type haddr();
   method Bool hwrite();
   method Bit#(2) htrans();

   // End Master Interface
   // ----------------------------------------------------------------
endinterface: Master_ifc 


// ====================================================================================
interface Slave_ifc #(type addr_type, type data_type, type resp_type, type status_type);

   // ----------------------------------------------------------------
   // Slave Interface

   // address phase
   // EN_s_hready_in = s_hready_in
   method Action hready_in ( Bool      s_hsel,
                            addr_type s_haddr,
                            Bool      s_hwrite,
                            Bit#(2)   s_htrans);
      
   method Action write_data (data_type s_hwdata,
                             Bit#(2)   s_htrans);
   method Bool hready_out();
      
   method data_type hrdata();
      
   method resp_type hresp();
      
   // End Slave Interface
   // ----------------------------------------------------------------
endinterface: Slave_ifc

 
interface Slave_DMAC_ifc #(type addr_type, type data_type, type resp_type, type status_type);
// ----------------------------------------------------------------
// Slave Interface

   // address phase
   // EN_s_hready_in = s_hready_in
   method Action hready_in ( Bool s_hsel,        
                               addr_type s_haddr,  
                               Bool s_hwrite);     

   method Action write_data (data_type s_hwdata);
   method Bool hready_out();
   
   method data_type hrdata();
   method resp_type hresp();

// End Slave Interface
// ----------------------------------------------------------------
endinterface
