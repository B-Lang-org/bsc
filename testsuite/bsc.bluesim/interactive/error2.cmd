# Test script for error handling

# issue a command which returns a user error, and catch it
if [catch {puts [sim cd blah.sub]} err] then {
  puts "Caught error!"
  puts $err
}

# issue a command which returns a user error, but don't catch it
puts [sim cd mid1.blah]

puts "This command should not be reached"

# end of script

