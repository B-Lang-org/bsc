//
// either one of the sync signals
//
//       |<-- Active Region ---->|<----------- Blanking Region ---------->|
//       |      (Pixels)         |                                        |
//       |                       |                                        |
//       |                       |                                        |
//   ----+--------- ... ---------+-------------             --------------+---
//   |   |                       |            |             |             |
//   |   |                       |<--Front    |<---Sync     |<---Back     |
//   |   |                       |    Porch-->|     Time--->|    Porch--->|
// ---   |                       |            ---------------             |
//       |                       |                                        |
//       |<------------------- Period ----------------------------------->|
//

// Sync info for horizontal or vertical
typedef struct {
                  Integer activeSize;
                  Integer syncStart;
                  Integer syncEnd;
                  Integer totalSize;
              } VGAHVTiming;

// Sync info for VGA
typedef struct {
                  VGAHVTiming h;
                  VGAHVTiming v;
              } VGATiming;

// Better?
// 640  650  710  762    480  482  488  500
// 800  812  888  952    600  602  610  626

VGATiming vga640x480;
vga640x480 = VGATiming { h : VGAHVTiming { activeSize : 640,
                                           syncStart : 664,
                                           syncEnd : 760,
                                           totalSize : 800},
                         v : VGAHVTiming { activeSize : 480, 
                                           syncStart : 490, 
                                           syncEnd : 494, 
                                           totalSize : 526}};

VGATiming vga1280x480;
vga1280x480 = VGATiming { h : VGAHVTiming { activeSize : 1280,
                                            syncStart : 1328,
                                            syncEnd : 1520,
                                            totalSize : 1600},
                          v : VGAHVTiming { activeSize : 480, 
                                            syncStart : 490, 
                                            syncEnd : 494, 
                                            totalSize : 526}};

function VGATiming hzToTiming(Integer hz);
  function Integer nsCycles(Integer x);
    return (div((x * hz), 1000000000));
  endfunction: nsCycles
  function Integer usCycles(Integer x);
    return (div((x * hz), 1000000));
  endfunction: usCycles
  
  Integer hTotalSize;  
  hTotalSize =  nsCycles(31770);

  return (VGATiming { h : VGAHVTiming { activeSize : nsCycles(25170),
                                        syncStart : nsCycles(26110),
                                        syncEnd : nsCycles(29880),
                                        totalSize : hTotalSize},
                      v : VGAHVTiming { activeSize : div(usCycles(15250), hTotalSize),
                                        syncStart : div(usCycles(15700), hTotalSize),
                                        syncEnd : div(usCycles(15764), hTotalSize),
                                        totalSize : div(usCycles(16784), hTotalSize)}});
endfunction: hzToTiming

function VGATiming sizeToTiming(Integer hSize, Integer vSize);
  return (VGATiming { h : VGAHVTiming { activeSize : hSize,
                                        syncStart : div((hSize * 856), 800),
                                        syncEnd : div((hSize * 880), 800),
                                        totalSize : div((hSize * 982), 800)},
                      v : VGAHVTiming { activeSize : vSize,
                                        syncStart : div((vSize * 602), 600),
                                        syncEnd : div((vSize * 610), 600),
                                        totalSize : div((vSize * 626), 600)}});
endfunction: sizeToTiming

interface VGACore #(type hCoord, type vCoord);
    method Bool not_hsync();
    method Bool not_vsync();
    method Bool blank();
    method hCoord hPos();
    method vCoord vPos();
    method Bool lineTick();
    method Bool frameTick();
endinterface: VGACore

module mkVGACore#(Integer preScale, VGATiming vt)(VGACore#(hCoord, vCoord))
  provisos (Bits#(hCoord, hs),
            Literal#(hCoord),
            Eq#(hCoord),
            Arith#(hCoord),
            Bits#(vCoord, vs),
            Literal#(vCoord),
            Eq#(vCoord),
            Arith#(vCoord));

    Reg#(hCoord) hPosR();
    mkReg#(0) the_hPosR(hPosR);
    Reg#(vCoord) vPosR();
    mkReg#(0) the_vPosR(vPosR);
    Reg#(Bool) hVisible();
    mkReg#(True) the_hVisible(hVisible);
    Reg#(Bool) vVisible();
    mkReg#(True) the_vVisible(vVisible);
    Reg#(Bool) not_hsyncR();
    mkReg#(True) the_not_hsyncR(not_hsyncR);
    Reg#(Bool) not_vsyncR();
    mkReg#(True) the_not_vsyncR(not_vsyncR);
    Reg#(Bit#(4)) scale();
    mkReg#(0) the_scale(scale);

    hCoord hSize;
    vCoord vSize;
    hCoord hSyncStart;
    vCoord vSyncStart;
    hCoord hSyncEnd;
    vCoord vSyncEnd;
    hCoord hTotal;
    vCoord vTotal;
    Bool hTickLocal;
    Bool vTickLocal;
    Bool hTickExternal;
    Bool vTickExternal;
  
    hSize =  fromInteger(vt.h.activeSize);
    vSize =  fromInteger(vt.v.activeSize);
    hSyncStart =  fromInteger(vt.h.syncStart);
    vSyncStart =  fromInteger(vt.v.syncStart);
    hSyncEnd =  fromInteger(vt.h.syncEnd);
    vSyncEnd =  fromInteger(vt.v.syncEnd);
    hTotal =  fromInteger(vt.h.totalSize);
    vTotal =  fromInteger(vt.v.totalSize);
    hTickLocal =  hPosR == hTotal;
    vTickLocal =  hTickLocal && (vPosR == vTotal);
    hTickExternal =  hPosR == (hSize + 1);
    vTickExternal =  hTickExternal && (vPosR == (vSize + 1));

    (* no_implicit_conditions, fire_when_enabled *)
    rule tick (preScale != 1); 
        scale <= (scale == 0 ? fromInteger(preScale - 1) : scale - 1);
    endrule: tick

    (* no_implicit_conditions, fire_when_enabled *)
    rule hclk ((preScale == 1) || (scale == 0));
        hPosR <= (hTickLocal ? 0 : hPosR + 1);
        hVisible <= ((hPosR != hSize) && (hTickLocal || hVisible));
    endrule: hclk

    (* no_implicit_conditions, fire_when_enabled *)
    rule vclk (hTickLocal);
        vPosR <= (vTickLocal ? 0 : vPosR + 1);
        vVisible <= ((vPosR != vSize) && (vTickLocal || vVisible));
    endrule: vclk

    (* no_implicit_conditions, fire_when_enabled *)
    rule hsyncOn (hPosR == hSyncStart); 
        not_hsyncR <= False;
    endrule: hsyncOn

    (* no_implicit_conditions, fire_when_enabled *)
    rule hsyncOff (hPosR == hSyncEnd); 
        not_hsyncR <= True;
    endrule: hsyncOff

    (* no_implicit_conditions, fire_when_enabled *)
    rule vsyncOn (vPosR == vSyncStart); 
        not_vsyncR <= False;
    endrule: vsyncOn

    (* no_implicit_conditions, fire_when_enabled *)
    rule vsyncOff (vPosR == vSyncEnd); 
        not_vsyncR <= True;
    endrule: vsyncOff

    method hPos(); 
      return (hPosR);
    endmethod: hPos
    method vPos(); 
      return (vPosR);
    endmethod: vPos
    // blank video outside of visible region
    method blank(); 
      return (!(hVisible && vVisible));
    endmethod: blank
    method not_hsync(); 
      return (not_hsyncR);
    endmethod: not_hsync
    method not_vsync(); 
      return (not_vsyncR);
    endmethod: not_vsync
    method lineTick(); 
      return (hTickExternal && vVisible);
    endmethod: lineTick
    method frameTick(); 
      return (vTickExternal);
    endmethod: frameTick

endmodule: mkVGACore
