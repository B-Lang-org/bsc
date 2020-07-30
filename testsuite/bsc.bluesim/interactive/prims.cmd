# Test script for error handling

sim step 5

# test the register
sim cd count
puts [sim ls]
puts [sim get [sim lookup ""]]

# test the wire
sim cd .w
puts [sim ls]
puts [sim get [sim lookup ""] [sim lookup "isValid"]]

# test the FIFO
sim cd
puts [sim ls fifo]
puts [sim ls fifo.*]
puts [sim get [sim lookup "fifo.level"]]
puts [sim getrange [sim lookup "fifo"] 0]
sim cd fifo
puts [sim ls]
puts [sim getrange [sim lookup ""] 0 1]

# test the RegFile
sim cd .rf
puts [sim ls]
puts [sim get [sim lookup "high_addr"]]
sim cd
puts [sim getrange [sim lookup "rf"] 0 10]

# test the Probe
sim cd
puts [sim ls "probe.*"]
puts [sim get [sim lookup "probe"]]

# end of script

