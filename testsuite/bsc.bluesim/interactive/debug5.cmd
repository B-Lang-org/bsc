# show rule firings

set level 0
set fireinfo []

proc find_rules {} {
  global fireinfo
  global level
  set level [expr $level + 1]
  set dir [sim pwd]
  set hdls []
  foreach entry [sim ls] {
    if {[lindex $entry 1] == "rule"} {
      set rl_name [lindex $entry 0]
      set wf_name [join [list "WILL_FIRE_" $rl_name] ""]
      set wf_hdl [sim lookup $wf_name]
      set cf_name [join [list "CAN_FIRE_" $rl_name] ""]
      set cf_hdl [sim lookup $cf_name]
      lappend hdls "$rl_name $cf_hdl $wf_hdl"
    }
  }
  lappend fireinfo "$level [sim pwd] $hdls"
  foreach entry [sim ls] {
    if {[lindex $entry 1] == "module"} {
      sim cd [lindex $entry 0]
      find_rules
      sim up
    }
  }
  set level [expr $level - 1]
}

find_rules

while {true} {
  if [catch {sim step}] {break}
  puts "---- Rules firing at [sim time] ----"
  foreach info $fireinfo {
    set lvl [lindex $info 0]
    set mod [lindex $info 1]
    set rls [lrange $info 2 end]
    set msgs []
    foreach rl $rls {
      set rl_name [lindex $rl 0]
      set cf_hdl  [lindex $rl 1]
      set wf_hdl  [lindex $rl 2]
      if {[sim get $wf_hdl] == "1'h1"} {
        lappend msgs "$rl_name fired"
      } elseif {[sim get $cf_hdl] == "1'h1"} {
        lappend msgs "$rl_name was blocked by a more urgent rule"
      }
    }
    if {[llength $msgs] != 0} {
      puts "In module $mod:"
      foreach msg $msgs {
        puts "  $msg"
      }
    }
  }
}
