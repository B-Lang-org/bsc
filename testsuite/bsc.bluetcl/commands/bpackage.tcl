namespace import ::Bluetcl::*

# output should be empty
puts [bpackage list]

# load a file
puts [bpackage load Test]
puts [bpackage list]

# clear the packages
puts [bpackage clear]
# list should be empty
puts [bpackage list]

# load the file again
puts [bpackage load Test]
puts [bpackage list]

# load a new file (should not remove any previous files)
puts [bpackage load RegFile]
puts [bpackage list]

# test the "depend" subcommand
puts "Depends: [bpackage depend]"

# test the "search" subcommand
puts "\nSearch Bar:"
puts [join [bpackage search Bar] "\n" ]

puts "\nSearch mkT:"
puts [join [bpackage search mkT] "\n"]

puts "\nSearch Reg:"
puts [join [bpackage search Reg] "\n" ]


