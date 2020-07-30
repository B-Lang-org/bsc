//////////////////////////////////////////////////////////////////////////////
//
// kbscan.v - simple PS/2-port byte scancode reader
//
// --------------------------------------------------------------------------
//
//   This module is a byte-level scancode reader for the PS/2-Keyboard device.
// Currently the reader allows only unidirectional communication 
// (device->host); output is not supported yet.
//
//   Module inputs are the kbclk/kbdata outputs from a PS/2 device.  
// Outputs are a byte-scancode and its parity-check status.  The module has 
// two main components, the input-scanner and the output byte-buffer.
//
//   The input-scanner contains a 4-bit counter, 10-bit shift-register, and
// a state-machine to generate control signals.  The output byte-buffer
// is a register storing the last received scancode.  The buffer also 
// stores its current state (empty or full), and the parity-status of the
// last received scancode.
//   The module can store up to 1 byte-scancode for a client, while
// simultaneously receiving the next-scancode.  Logically, this makes
// the reader a 2-stage pipeline.
//
//  Inputs : i_kbclk, i_kbdata (signal lines from the keyboard-device)
//           clk, rstn (synchronous logic signals for the flipflops, latch)
//
//  Outputs: o_byte (one byte scancode, valid when o_byte_rdy==1)
//           o_byte_rdy (ready line, 1=o_byte contains valid scancode)
//           o_byte_err (parity error status, 1=error)
//
//           * both o_byte_rdy and o_byte_err are cleared 1T after i_byte_ack
//
// Known limitations :
// -------------------
//   No transmit capability (from client to PS/2 device)
//   adherence to PS/2 electrical protocol may not be 100%
//   
//
// Want to know more about the Keyboard protocol?
// http://panda.cs.ndsu.nodak.edu/~achapwes/PICmicro/keyboard/atkeyboard.html
// http://www.repairfaq.org/filipg/LINK/PORTS/F_Keyboard_FAQ.html
//
// ... or do a google.com search on '8042 keyboard'
//
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//
//  Output byte-client timing
//  -------------------------
//  kbscan uses a very simple rdy/ack protocol.  When kbscan has received
//  a scancode, it raises the rdy flag.  kbscan forces kbclk LOW, to 
//  inhibit the PS/2-device from transmitting new scancodes.  After the
//  byte-client reads the data, it raises the ack flag for 1T.  
//  When kbscan receives ack, it internally resets, releases kbclk (to allow
//  incoming scancodes), and waits for the next scancode.
//         _   _   _   _   _   _   _   _   _   _   _   _
//  clk |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_|
//                                  ___
//  i_byte_ack ____________________|   |___________
//                  ___________________
//  o_byte_rdy ____|                   |___________
//                  ___________________
//  o_byte_err ____|:ERROR:STATUS::::::|___________
//                  ___________________
//  o_byte     XXXX< new_data  ________>XXXXXXXXXXX
//
//////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////// -----
//
//   liaor@iname.com - http://members.tripod.com/~liaor  (05/01/2001)
//
//   This program is free software; you can redistribute it and/or
//  modify it under the terms of the GNU General Public License
//  as published by the Free Software Foundation; either version 2
//  of the License, or (at your option) any later version.
//  
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU General Public License for more details.
//  
//  You should have received a copy of the GNU General Public License
//  along with this program; if not, write to the Free Software
//  Foundation, Inc., http://www.gnu.org
//
/////////////////////////////////////////////////////////////////////////////

module kbscan(
  // inputs
    clk, rstn, 
    i_kbclk, i_kbdata, i_byte_ack,
  // outputs
    o_byte, o_byte_rdy, o_byte_err, o_kbclk_en
   );

//parameter SM_0 = 0;
parameter SM_1 = 0;
parameter SM_2 = 1;
   
parameter S_W = 10; // shift register width (DO NOT CHANGE)
parameter BYTE_ERROR = 8'd0;  // error-code to flag parity-error
parameter KBCNT = 11; // 11 clocks

input  clk;              // system clock
input  rstn;             // async global reset (active low)

input  i_kbclk;          // Keybaord clock line
input  i_kbdata;         // Keyboard data line
input  i_byte_ack;       // byte acknolwedge

output       o_byte_rdy; // Byte data ready (cleared on i_byte_ack)
output       o_byte_err; // Byte parity error (1=error, cleared on i_byte_ack)
output [7:0] o_byte;     // Byte-scancode (valid on o_byte_rdy)
output       o_kbclk_en; // enable-input on kbclk (1=allow in, 0=force low)

// reg'd versions of inputs, for synchronization to local master clock (clk)
reg    r_kbclk;          // reg'd (synchronized) kbclk
reg    r_kbdata;         // reg'd (synchronized) kbdata

reg    r_kbclk_1d;       // 1 clk delayed version of r_kbclk
reg    kbclk_stb;        // pulse on negedge of r_kbclk


// Component (1) : input-scanner
reg  [(S_W-1):0] s_reg;        // input (kbdata) shift register
reg              s_reg_err;    // final parity result on s_reg (1=error)
reg              s_reg_parity; // s_reg's running parity

reg        fsm_ps, fsm_ns;    // state-machine 
reg        fsm_lock_kbclkn, fsm_lock_kbclkn_ns;  // control, 'lock kbclk'

reg  [3:0] kbclk_ctr;
reg        kbclk_ctr_eqcnt;
wire       kbclk_ctr_eqcnt_ns;
wire       kbclk_ctr_reset;

// Component (2) : output buffer logic
reg  [7:0] o_byte;       // byte data register (last received scancode)
reg        o_byte_rdy;   // byte-status, (1=contain valid data, 0=empty)
reg        o_byte_err;   // o_byte parity error status (1=error, 0=ok)
wire       o_byte_load;  // control, load s_reg into o_byte

//////////////////////////////////////////////////////////////////////////////
//
// module inputs
//

  // In the top-level Xilinx schematic, the signals are brought in and
  // registered in the IO PADs.  Why do we need the additional register in 
  // this module?  The second register on the input signals (kbclk, kbdata) 
  // addresses metastability.
  always @ (posedge clk or negedge rstn )
  begin
    if ( !rstn )
      begin
        kbclk_stb<= 1'b0;
        r_kbclk_1d <= 1'b0;
        r_kbclk    <= 1'b0;
        r_kbdata   <= 1'b0;
      end
    else
      begin
        kbclk_stb<= (!r_kbclk) && (r_kbclk_1d);  // negedge of r_kbclk
        r_kbclk_1d <= r_kbclk;
        r_kbclk <= i_kbclk;
        r_kbdata <= i_kbdata;
      end
  end

//////////////////////////////////////////////////////////////////////////////
//
// Input-scanner : Finite State Machine Controller
//

  // This state machine performs the following actions in order:
  //   1) Countdown 1 complete scancode byte.  (Sit here until we capture 
  //      1 incoming byte scancode from the keyboard-device.)
  //
  //   2) assert o_kbclk_en, which controls a tristate-driver on kbclk.
  //      (the driver forces kbclk to 1'b0.  This tells keyboard-device to
  //       wait.)
  //
  //   3) Check the output-buffer status (o_byte_rdy.)
  //      Wait until (o_byte_rdy==0), indicating the output-buffer is free.
  //
  //   4) Transfer the captured byte-scancode to o_byte.  Assert o_byte_rdy
  //      ('byte ready') to indicate valid data in o_byte.  Then
  //      shut off the tristate-driver on kbclk (o_kbclk_en.)  Return to 1.
  //
  // Notice that this state machine does NOT wait for i_byte_ack...
  // Instead of checking i_byte_ack, the state-machine checks o_byte_rdy.
  // If (o_byte_rdy==1), the output-buffer o_byte is full (has data), so
  // it can't accept new data.
  // If (o_byte_rdy==0), the output-buffer o_byte is empty (no data), so
  // it can accept new data.
  
// generate next_state equations : COMBINATIONAL LOGIC ONLY
always @( fsm_ps or kbclk_ctr_reset or o_byte_load )
begin
  fsm_ns = fsm_ps;
  fsm_lock_kbclkn_ns = 1'b1;  // 1=don't lock kbclk, 0=lock kbclk
  case (fsm_ps)
        
    SM_1 : // READ SCANCODE
    begin 
      fsm_lock_kbclkn_ns = 1'b1;  // don't lock kbclk
      if (  kbclk_ctr_reset )  // kbclk_ctr_reset also clears the latch -> 0
        begin
          fsm_ns = SM_2; // after 1 complete scancode (11bits), go to SM_2
          fsm_lock_kbclkn_ns = 1'b0;  // force lock on keyboard
        end
    end
        
    SM_2 : // BYTE (scancode) ready for output-buffer (o_byte)
    begin
      fsm_lock_kbclkn_ns = 1'b0;  // force lock on keyboard
      if ( o_byte_load )  // wait for previous scancode to leave o_byte
        begin
          fsm_ns = SM_1;
          fsm_lock_kbclkn_ns = 1'b1;  // don't lock kbclk
        end
    end
      
    default :
      fsm_ns = SM_1;
  endcase
end

// the state-registers
always @ (posedge clk or negedge rstn )
begin
  if ( !rstn )
    begin
      fsm_ps <= SM_1;
      fsm_lock_kbclkn <= 1'b0;  // force lock on keyboard
    end
  else
    begin
      fsm_ps <= fsm_ns;
      fsm_lock_kbclkn <= fsm_lock_kbclkn_ns;
    end
end
    

////////////////////////

always @ (posedge clk or negedge rstn )
begin
  if ( !rstn )
    begin
      s_reg <= 0;
      s_reg_parity <= 1'b0;  // working (temp) parity of s_reg
      s_reg_err <= 1'b0;     // final parity check result on s_reg 
      kbclk_ctr <= 0;
      kbclk_ctr_eqcnt <= 1'b0;
    end
  else
    begin
      if ( kbclk_stb )
        begin
          // shift data in from MSB, shift right
          s_reg <= {r_kbdata, s_reg[(S_W-1):1]}; 
        end
        
      kbclk_ctr_eqcnt <= kbclk_ctr_eqcnt_ns;
      
      if ( kbclk_ctr_reset )
        begin
          kbclk_ctr <= 0;
          s_reg_parity <= 1'b0;
          s_reg_err <= s_reg_parity; // get final-parity result
        end
      else if ( kbclk_stb )
        begin
          kbclk_ctr <= kbclk_ctr + 1;
          s_reg_parity <= s_reg_parity ^ r_kbdata;
        end
    end
end
assign kbclk_ctr_reset = kbclk_ctr_eqcnt; // glitchless (reg'd signal)
assign kbclk_ctr_eqcnt_ns = (kbclk_ctr ==(KBCNT-1) && kbclk_stb);// next-state	

// time ->
//                                           !     kbclk_ctr_eqcnt_ns
//   !   !   !   !   !   !   !   !   !   !   !   ! kbclk_stb (negedge r_kbclk)
// __   _   _   _   _   _   _   _   _   _   _   _
//   |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| \_force_low
//___ ___ ___ ___ ___ ___ ___ ___ ___ ___ ___ ___ 
// 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |10 |11   kbclk_ctr
//
// -<S>-<0>-<1>-<2>-<3>-<4>-<5>-<6>-<7>-<P>-<T>-   r_kbdata
//                                        _ns rst
//  S=start(1'b1), P=parity(odd), T=stop(1'b0)   
//


//////////////////////////////////////////////////////////////////////////////
//
// module output stage
//

  // o_byte is the output data-register, which serves as a single byte buffer.
  //
  // The status signal o_byte_rdy serves 2 purposes :
  //   1) tell client if a scancode is available.  o_byte_rdy==1 means 
  //      data is available and the client should read it.  (Client raises
  //      i_byte_ack to signify it has received the data from kbscan.)
  //   2) tell the kbscan statemachine if output-buffer is ready for new
  //      data.  o_byte_rdy means the output buffer is empty, and can accept
  //      new scancode.

  always @ (posedge clk or negedge rstn )
  begin
    if ( !rstn )
      begin
        o_byte <= BYTE_ERROR;
        o_byte_rdy <= 1'b0;
        o_byte_err <= 1'b0;
      end
    else if ( o_byte_load )  // transfer data from s_reg?
      begin
        o_byte <= s_reg_err ? BYTE_ERROR : s_reg[7:0]; 
        o_byte_rdy <= 1'b1;  // raise rdy line, got new data!
        o_byte_err <= s_reg_err; // load parity status: 1=error, 0=no error
      end
    else if ( i_byte_ack )  // byte acknowledged?
      begin
//        o_byte <= BYTE_ERROR;
        o_byte_rdy <= 1'b0;  // lower rdy line, output buffer is now empty
        o_byte_err <= 1'b0;  // clear error-flag on ack
      end
  end
  assign o_byte_load =  (fsm_ps==SM_2) && (o_byte_rdy==0); 
  assign o_kbclk_en = fsm_lock_kbclkn;  // 1=enable input, 0=disable input

endmodule
