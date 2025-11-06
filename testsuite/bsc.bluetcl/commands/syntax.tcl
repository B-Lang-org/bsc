# We can keep setting the syntax until the first time it is read.
puts [Bluetcl::syntax set bh]
puts [Bluetcl::syntax set bsv]
puts [Bluetcl::syntax set bh]
puts [Bluetcl::syntax get]

if { [catch {Bluetcl::syntax set bsv}] } {
    puts "Bluetcl::syntax set fails after syntax is frozen."
} else {
    error "Bluetcl::syntax set should fail after Bluetcl::syntax get"
}

