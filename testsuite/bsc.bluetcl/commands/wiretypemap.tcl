namespace import ::Bluetcl::*

proc dumpMap { mod }  {
    puts "Command: module wiretypemap $mod"
    if { [catch [list module wiretypemap $mod] err] } {
        puts "Caught error:  $err"
    } else {
        # Sort for deterministic output across runs
        foreach entry [lsort $err] {
            puts "$entry"
        }
    }
    puts "---------"
}

puts [flags set {-verilog}]
puts [module load mkWireTypes]

puts {----------}

# Exercise rich types: struct (Pixel), tagged union (Cell), enum
# (Color), Vector#(4, Color), Maybe#(Pixel), plus polymorphic
# primitives (Reg/FIFOF/BRAM/SyncFIFO/CReg/RWire/BypassWire/PulseWire).
dumpMap mkWireTypes

# Hierarchical case: mkPixelStash is a separately-synthesized leaf
# instantiated as leafA and leafB inside mkWireTypes. The per-module
# wiretypemap is keyed by module name (not instance), so one query
# covers all instances of that module. This is what makes per-.ba
# wiretypemap consumption efficient -- you compute the map once and
# match every instance of that module at any scope in the design
# hierarchy.
dumpMap mkPixelStash
