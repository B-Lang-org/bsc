
`ifdef BSV_ASSIGNMENT_DELAY
`else
 `define BSV_ASSIGNMENT_DELAY
`endif

// Single-Ported BRAM
module BRAM1Load(CLK,
                 EN,
                 WE,
                 ADDR,
                 DI,
                 DO
                 );

   parameter                      FILENAME   = "";
   parameter                      PIPELINED  = 0;
   parameter                      ADDR_WIDTH = 1;
   parameter                      DATA_WIDTH = 1;
   parameter                      MEMSIZE    = 1;
   parameter                      BINARY     = 0;

   input                          CLK;
   input                          EN;
   input                          WE;
   input [ADDR_WIDTH-1:0]         ADDR;
   input [DATA_WIDTH-1:0]         DI;
   output [DATA_WIDTH-1:0]        DO;

   wire                           REN = EN & !WE;
   wire                           WEN = EN & WE;
      
   altsyncram
     #(
       .width_a                            (DATA_WIDTH),
       .widthad_a                          (ADDR_WIDTH),
       .numwords_a                         (MEMSIZE),
       .outdata_reg_a                      ((PIPELINED) ? "CLOCK0" : "UNREGISTERED"),
       .address_aclr_a                     ("NONE"),
       .outdata_aclr_a                     ("NONE"),
       .indata_aclr_a                      ("NONE"),
       .wrcontrol_aclr_a                   ("NONE"),
       .byteena_aclr_a                     ("NONE"),
       .width_byteena_a                    (1),

       .width_b                            (1),//
       .widthad_b                          (1),//
       .numwords_b                         (0),//
       .rdcontrol_reg_b                    ("CLOCK1"),//
       .address_reg_b                      ("CLOCK1"),//
       .outdata_reg_b                      ("UNREGISTERED"),//
       .outdata_aclr_b                     ("NONE"),//
       .rdcontrol_aclr_b                   ("NONE"),//
       .indata_reg_b                       ("CLOCK1"),//
       .wrcontrol_wraddress_reg_b          ("CLOCK1"),//
       .byteena_reg_b                      ("CLOCK1"),//
       .indata_aclr_b                      ("NONE"),//
       .wrcontrol_aclr_b                   ("NONE"),//
       .address_aclr_b                     ("NONE"),//
       .byteena_aclr_b                     ("NONE"),//
       .width_byteena_b                    (1),//

       .clock_enable_input_a               ("BYPASS"),
       .clock_enable_output_a              ("BYPASS"),
       .clock_enable_input_b               ("NORMAL"),//
       .clock_enable_output_b              ("NORMAL"),//

       .clock_enable_core_a                ("USE_INPUT_CLKEN"),//
       .clock_enable_core_b                ("USE_INPUT_CLKEN"),//
       .read_during_write_mode_port_a      ("OLD_DATA"),
       .read_during_write_mode_port_b      ("NEW_DATA_NO_NBE_READ"),

       .enable_ecc                         ("FALSE"),//
       .width_eccstatus                    (3),//
       .ecc_pipeline_stage_enabled         ("FALSE"),//

       .operation_mode                     ("SINGLE_PORT"),
       .byte_size                          (8),//
       .read_during_write_mode_mixed_ports ("DONT_CARE"),//
       .ram_block_type                     ("AUTO"),//
       .init_file                          (FILENAME),//
       .init_file_layout                   ("PORT_A"),//
       .maximum_depth                      (MEMSIZE), // number of elements in memory
       .intended_device_family             ("Stratix"),//
       .lpm_hint                           ("ENABLE_RUNTIME_MOD=NO"),
       .lpm_type                           ("altsyncram"),//
       .implement_in_les                   ("OFF"), //
       .power_up_uninitialized             ("FALSE")
       )
   RAM
     (
      .wren_a                              (WEN),
      .rden_a                              (REN),
      .data_a                              (DI),
      .address_a                           (ADDR),
      .clock0                              (CLK),
      .clocken0                            (1'b1),
      .clocken1                            (1'b1),
      .aclr0                               (1'b0),
      .byteena_a                           (1'b1),
      .addressstall_a                      (1'b0),
      .q_a                                 (DO),

      .wren_b                              (1'b0),
      .rden_b                              (1'b1),
      .data_b                              (1'b1),
      .address_b                           (1'b1),
      .clock1                              (1'b1),
      .clocken2                            (1'b1),
      .clocken3                            (1'b1),
      .aclr1                               (1'b0),
      .byteena_b                           (1'b1),
      .addressstall_b                      (1'b0),
      .q_b                                 (),

      .eccstatus                           ()
      );

endmodule // BRAM1Load
