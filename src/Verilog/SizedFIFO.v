
`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif

`ifdef BSV_ASYNC_RESET
 `define BSV_ARESET_EDGE_META or `BSV_RESET_EDGE RST
`else
 `define BSV_ARESET_EDGE_META
`endif

`ifdef BSV_RESET_FIFO_HEAD
 `define BSV_ARESET_EDGE_HEAD `BSV_ARESET_EDGE_META
`else
 `define BSV_ARESET_EDGE_HEAD
`endif

`ifdef BSV_RESET_FIFO_ARRAY
 `define BSV_ARESET_EDGE_ARRAY `BSV_ARESET_EDGE_META
`else
 `define BSV_ARESET_EDGE_ARRAY
`endif


// Sized fifo.  Model has output register which improves timing
module SizedFIFO(CLK, RST, D_IN, ENQ, FULL_N, D_OUT, DEQ, EMPTY_N, CLR);
   parameter               p1width = 1; // data width
   parameter               p2depth = 3;
   parameter               p3cntr_width = 1; // log(p2depth-1)
   // The -1 is allowed since this model has a fast output register
   parameter               guarded = 1'b1;
   localparam              p2depth2 = (p2depth >= 2) ? (p2depth -2) : 0 ;

   input                   CLK;
   input                   RST;
   input                   CLR;
   input [p1width - 1 : 0] D_IN;
   input                   ENQ;
   input                   DEQ;

   output                  FULL_N;
   output                  EMPTY_N;
   output [p1width - 1 : 0] D_OUT;

   reg                      not_ring_full;
   reg                      ring_empty;

   reg [p3cntr_width-1 : 0] head;
   wire [p3cntr_width-1 : 0] next_head;

   reg [p3cntr_width-1 : 0]  tail;
   wire [p3cntr_width-1 : 0] next_tail;

   // if the depth is too small, don't create an ill-sized array;
   // instead, make a 1-sized array and let the initial block report an error
   reg [p1width - 1 : 0]     arr[0: p2depth2];

   reg [p1width - 1 : 0]     D_OUT;
   reg                       hasodata;

   wire [p3cntr_width-1:0]   depthLess2 = p2depth2[p3cntr_width-1:0] ;

   wire [p3cntr_width-1 : 0] incr_tail;
   wire [p3cntr_width-1 : 0] incr_head;

   assign                    incr_tail = tail + 1'b1 ;
   assign                    incr_head = head + 1'b1 ;

   assign    next_head = (head == depthLess2 ) ? {p3cntr_width{1'b0}} : incr_head ;
   assign    next_tail = (tail == depthLess2 ) ? {p3cntr_width{1'b0}} : incr_tail ;

   assign    EMPTY_N = hasodata;
   assign    FULL_N  = not_ring_full;

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
     begin : initial_block
        integer   i;
        D_OUT         = {((p1width + 1)/2){2'b10}} ;

        ring_empty    = 1'b1;
        not_ring_full = 1'b1;
        hasodata      = 1'b0;
        head          = {p3cntr_width {1'b0}} ;
        tail          = {p3cntr_width {1'b0}} ;

        for (i = 0; i <= p2depth2; i = i + 1)
          begin
             arr[i]   = D_OUT ;
          end
     end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS


   always @(posedge CLK `BSV_ARESET_EDGE_META)
     begin
        if (RST == `BSV_RESET_VALUE)
          begin
             head <= `BSV_ASSIGNMENT_DELAY {p3cntr_width {1'b0}} ;
             tail <= `BSV_ASSIGNMENT_DELAY {p3cntr_width {1'b0}} ;
             ring_empty <= `BSV_ASSIGNMENT_DELAY 1'b1;
             not_ring_full <= `BSV_ASSIGNMENT_DELAY 1'b1;
             hasodata <= `BSV_ASSIGNMENT_DELAY 1'b0;
          end // if (RST == `BSV_RESET_VALUE)
        else
         begin

             casez ({CLR, DEQ, ENQ, hasodata, ring_empty})
               // Clear operation
               5'b1????: begin
                  head          <= `BSV_ASSIGNMENT_DELAY {p3cntr_width {1'b0}} ;
                  tail          <= `BSV_ASSIGNMENT_DELAY {p3cntr_width {1'b0}} ;
                  ring_empty    <= `BSV_ASSIGNMENT_DELAY 1'b1;
                  not_ring_full <= `BSV_ASSIGNMENT_DELAY 1'b1;
                  hasodata      <= `BSV_ASSIGNMENT_DELAY 1'b0;
               end
               // -----------------------
               // DEQ && ENQ case -- change head and tail if added to ring
               5'b011?0: begin
                  tail          <= `BSV_ASSIGNMENT_DELAY next_tail;
                  head          <= `BSV_ASSIGNMENT_DELAY next_head;
               end
               // -----------------------
               // DEQ only and NO data is in ring
               5'b010?1: begin
                  hasodata <= `BSV_ASSIGNMENT_DELAY 1'b0;
               end
               // DEQ only and data is in ring (move the head pointer)
               5'b010?0: begin
                  head          <= `BSV_ASSIGNMENT_DELAY next_head;
                  not_ring_full <= `BSV_ASSIGNMENT_DELAY 1'b1;
                  ring_empty    <= `BSV_ASSIGNMENT_DELAY next_head == tail ;
               end
               // -----------------------
               // ENQ only when empty
               5'b0010?: begin
                  hasodata      <= `BSV_ASSIGNMENT_DELAY 1'b1;
                  end
               // ENQ only when not empty
               5'b0011?: begin
                  if ( not_ring_full ) // Drop this test to save redundant test
                    // but be warnned that with test fifo overflow causes loss of new data
                    // while without test fifo drops all but head entry! (pointer overflow)
                   begin
                      tail          <= `BSV_ASSIGNMENT_DELAY next_tail;
                      ring_empty    <= `BSV_ASSIGNMENT_DELAY 1'b0;
                      not_ring_full <= `BSV_ASSIGNMENT_DELAY ! (next_tail == head) ;
                   end
               end
             endcase
         end // else: !if(RST == `BSV_RESET_VALUE)
     end // always @ (posedge CLK)

   // Update the fast data out register
   always @(posedge CLK `BSV_ARESET_EDGE_HEAD)
     begin
`ifdef  BSV_RESET_FIFO_HEAD
        if (RST == `BSV_RESET_VALUE)
          begin
             D_OUT    <= `BSV_ASSIGNMENT_DELAY {p1width {1'b0}} ;
          end // if (RST == `BSV_RESET_VALUE)
        else
`endif
        begin
             casez ({CLR, DEQ, ENQ, hasodata, ring_empty})
               // DEQ && ENQ cases
               5'b011?0: begin D_OUT <= `BSV_ASSIGNMENT_DELAY arr[head]; end
               5'b011?1: begin D_OUT <= `BSV_ASSIGNMENT_DELAY D_IN; end
               // DEQ only and data is in ring
               5'b010?0: begin D_OUT <= `BSV_ASSIGNMENT_DELAY arr[head]; end
               // ENQ only when empty
               5'b0010?: begin D_OUT <= `BSV_ASSIGNMENT_DELAY D_IN; end
             endcase
          end // else: !if(RST == `BSV_RESET_VALUE)
     end // always @ (posedge CLK)

   // Update the memory array  reset is OFF
   always @(posedge CLK `BSV_ARESET_EDGE_ARRAY)
     begin: array
`ifdef BSV_RESET_FIFO_ARRAY
        if (RST == `BSV_RESET_VALUE)
          begin: rst_array
             integer i;
             for (i = 0; i <= p2depth2 && p2depth > 2; i = i + 1)
               begin
                   arr[i]  <= `BSV_ASSIGNMENT_DELAY {p1width {1'b0}} ;
               end
          end // if (RST == `BSV_RESET_VALUE)
        else
`endif
         begin
            if (!CLR && ENQ && ((DEQ && !ring_empty) || (!DEQ && hasodata && not_ring_full)))
              begin
                 arr[tail] <= `BSV_ASSIGNMENT_DELAY D_IN;
              end
         end // else: !if(RST == `BSV_RESET_VALUE)
     end // always @ (posedge CLK)

   // synopsys translate_off
   always@(posedge CLK)
     begin: error_checks
        reg deqerror, enqerror ;

        deqerror =  0;
        enqerror = 0;
        if (RST == ! `BSV_RESET_VALUE)
           begin
              if ( ! EMPTY_N && DEQ )
                begin
                   deqerror = 1 ;
                   $display( "Warning: SizedFIFO: %m -- Dequeuing from empty fifo" ) ;
                end
              if ( ! FULL_N && ENQ && (!DEQ || guarded) )
                begin
                   enqerror =  1 ;
                   $display( "Warning: SizedFIFO: %m -- Enqueuing to a full fifo" ) ;
                end
           end
     end // block: error_checks
   // synopsys translate_on

   // synopsys translate_off
   // Some assertions about parameter values
   initial
     begin : parameter_assertions
        integer ok ;
        ok = 1 ;

        if ( p2depth <= 1)
          begin
             ok = 0;
             $display ( "Warning SizedFIFO: %m -- depth parameter increased from %0d to 2", p2depth);
          end

        if ( p3cntr_width <= 0 )
          begin
             ok = 0;
             $display ( "ERROR SizedFIFO: %m -- width parameter must be greater than 0" ) ;
          end

        if ( ok == 0 ) $finish ;

      end // initial begin
   // synopsys translate_on

endmodule
