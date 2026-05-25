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

# Exercise rich types: struct (Pixel), tagged union (Cell),
# enum (Color), Vector#(4, Color), Maybe#(Pixel), plus a
# FIFOF submodule whose ports carry the tagged-union type.
dumpMap mkWireTypes
