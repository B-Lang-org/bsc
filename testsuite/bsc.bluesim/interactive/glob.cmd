# Test script for the pattern globbing features

puts "*"
puts [sim ls *]
puts "-------"

puts "mid?.CAN_FIRE_*"
puts [sim ls mid?.CAN_FIRE_*]
puts "-------"

puts {RL_[a-f]*}
puts [sim ls {RL_[a-f]*}]
puts "-------"

puts {RL_[di]*}
puts [sim ls {RL_[di]*}]
puts "-------"

puts {*[id]*}
puts [sim ls {*[di]*}]
puts "-------"

puts {mid[0-9].*}
puts [sim ls {mid[0-9].*}]
puts "-------"

puts "*1"
puts [sim ls *1]
puts "-------"

puts {m*[12].RL_*}
puts [sim ls {m*[12].RL_*}]
puts "-------"

puts {?[!ie]*}
puts [sim ls {?[!ie]*}]
puts "-------"

puts {*FIRE_RL_?[]a-zA-Z]*[-npw-z]*}
puts [sim ls {*FIRE_RL_?[]a-zA-Z]*[-npw-z]*}]
puts "-------"

# end of script

