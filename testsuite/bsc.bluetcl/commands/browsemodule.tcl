namespace import ::Bluetcl::*

puts [flags set {-verilog}]
puts [module load mkT]

# display root
puts [browsemodule list 0]
# display top module (mkT)
puts [browsemodule list 1]
# display first submod (mkM)
puts [browsemodule list 2]
# display a RegN module
puts [browsemodule list 7]

# display detail on a primitive module
puts [browsemodule detail 7]
# display detail on a user module
puts [browsemodule detail 2]
for { set i 1 } { $i < 10 } { incr i } {
    puts "$i -----------"
    puts [browsemodule list $i]
    puts [browsemodule detail $i]
}
puts "top level "
utils::ldisplay [browsemodule detail 1]

# test refresh (used when the loaded module has changed)
puts [module load mkM]
puts [browsemodule refresh]
# redisplay the root
puts [browsemodule list 0]

for { set i 1 } { $i < 5 } { incr i } {
    puts "$i -----------"
    puts [browsemodule list $i]
    puts [browsemodule detail $i]
}
