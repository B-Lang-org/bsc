/**
 * Name: bsv
 * Description: Bluespec SystemVerilog hardware description language
 * Author: Ed Czeck <czeck@bluespec.com>  with credit to
 * Edward Arthur <eda@ultranet.com>, who developed the Verilog mode.
 * Date:  16 February 2005
 */

state bsv extends HighlightEntry
{
  /* Bluespec SystemVerilog takes C++ style comments */

  /* Comments. */
  /\/\// {
    comment_face (true);
    language_print ($0);
    call (eat_one_line);
    comment_face (false);
  }
  /\/\*/ {
    comment_face (true);
    language_print ($0);
    call (c_comment);
    comment_face (false);
  }

  /* String constants. */
  /\"/ {
    string_face (true);
    language_print ($0);
    call (c_string);
    string_face (false);
  }

  /* Macro expansions start with '`' and continue one word. */
  /`([a-zA-Z_0-9]+)/ {
    reference_face (true);
    language_print ($0);
    reference_face (false);
  }

  /* Types are capitalized names */
  /\b[A-Z][A-Za-z0-9_]+\b/ {
    type_face (true);
    language_print ($0);
    type_face (false);
  }    

  /* Keywords.
     (build-re '(always and assign begin buf bufif0 bufif1 case casex
     casez cmos deassign default defparam disable edge else end endcase
     endmodule endfunction endprimitive endspecify endtable endtask event
     for force forever fork function highz0 highz1 if initial inout input
     integer join large macromodule medium module nand negedge nmos nor
     not notif0 notif1 or output parameter pmos posedge primitive pull0
     pull1 pullup pulldown rcmos reg release repeat rnmos rpmos rtran
     rtranif0 rtranif1 scalared small specify specparam strength strong0
     strong1 supply0 supply1 table task time tran tranif0 tranif1 tri tri0
     tri1 triand trior trireg vectored wait wand weak0 weak1 while wire wor
     xnor xor
     rule endrule action endaction interface endinterface method endmethod
     package endpackage actionvalue endactionvalue instance endinstance
     typeclass endtypeclass rules endrules 
     typedef deriving import export provisos return struct type enum
     let match matches tagged union void 
     $bitstoreal $countdrivers $display $fclose $fdisplay $fmonitor
     $fopen $fstrobe $fwrite $finish $getpattern $history $incsave $input
     $itor $key $list $log $monitor $monitoroff $monitoron $nokey $nolog
     $printtimescale $readmemb $readmemh $realtime $realtobits $reset
     $reset_count $reset_value $restart $rtoi $save $scale $scope
     $showscopes $showvariables $showvars $sreadmemb $sreadmemh $stime
     $stop $strobe $time $timeformat $write $vcdpluson $vcdplusoff
     $vcdplustraceon $vcdplustraceoff $dumpvars
     ;; prefix G stands for grave `
     Gaccelerate Gautoexpand_vectornets Gcelldefine Gdefault_nettype Gdefine
     Gelse Gendcelldefine Gendif Gendprotect Gendprotected
     Gexpand_vectornets Gifdef Ginclude Gnoaccelerate
     Gnoexpand_vectornets Gnoremove_gatenames Gnoremove_netnames
     Gnounconnected_drive Gprotect Gprotected Gremove_gatenames
     Gremove_netnames Gresetall Gtimescale Gunconnected_drive
     Guselib
     ))
   */
  /\b($(bitstoreal|countdrivers|d(isplay|umpvars)\
|f(close|display|inish|monitor|open|strobe|write)|getpattern|history\
|i(n(csave|put)|tor)|key|l(ist|og)|monitor(|o(ff|n))|no(key|log)\
|printtimescale\
|r(e(a(dmem(b|h)|lt(ime|obits))|s(et(|_(count|value))|tart))|toi)\
|s(ave|c(ale|ope)|how(scopes|var(iables|s))|readmem(b|h)|t(ime|op|robe))\
|time(|format)|vcdplus(o(ff|n)|traceo(ff|n))|write)\
|G(a(ccelerate|utoexpand_vectornets)|celldefine|def(ault_nettype|ine)\
|e(lse|nd(celldefine|if|protect(|ed))|xpand_vectornets)|i(fdef|nclude)\
|no(accelerate|expand_vectornets|remove_(gatenames|netnames)\
|unconnected_drive)\
|protect(|ed)|re(move_(gatenames|netnames)|setall)|timescale\
|u(nconnected_drive|selib))\
|a(ction(|value)|lways|nd|ssign)|b(egin|uf(|if(0|1)))|c(ase(|x|z)|mos)\
|d(e(assign|f(ault|param)|riving)|isable)\
|e(dge|lse\
|n(d(|action(|value)|case|function|in(stance|terface)|m(ethod|odule)\
|p(ackage|rimitive)|rule(|s)|specify|t(a(ble|sk)|ypeclass))\
|um)\
|vent|xport)\
|f(or(|ce|ever|k)|unction)|highz(0|1)\
|i(f|mport|n(itial|out|put|stance|te(ger|rface)))|join|l(arge|et)\
|m(a(cromodule|tch(|es))|e(dium|thod)|odule)\
|n(and|egedge|mos|o(r|t(|if(0|1))))|o(r|utput)\
|p(a(ckage|rameter)|mos|osedge|r(imitive|ovisos)|ull(0|1|down|up))\
|r(cmos|e(g|lease|peat|turn)|nmos|pmos|tran(|if(0|1))|ule(|s))\
|s(calared|mall|pec(ify|param)|tr(ength|ong(0|1)|uct)|upply(0|1))\
|t(a(ble|gged|sk)|ime|r(an(|if(0|1))|i(|0|1|and|or|reg))|ype(|class|def))\
|union|v(ectored|oid)|w(a(it|nd)|eak(0|1)|hile|ire|or)|x(nor|or))\b/ {
    keyword_face (true);
    language_print ($0);
    keyword_face (false);
  }
}


/*
Local variables:
mode: c
End:
*/
