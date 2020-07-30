sim cd gcd

# get handles for start method enable and arguments
set hdl_of(EN_start)   [sim lookup EN_start]
set hdl_of(num1)       [sim lookup start_num1]
set hdl_of(num2)       [sim lookup start_num2]

# step and log start method calls
while {true} {
  if [catch {sim step}] {break}
  if {[sim get $hdl_of(EN_start)] == "1'h1"} {
     set num1 [sim get $hdl_of(num1)]
     set num2 [sim get $hdl_of(num2)]
     puts "[sim time]: start($num1,$num2)"
  }
}