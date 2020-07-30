namespace import ::Bluetcl::*
source pprint.tcl

puts [bpackage load Test]
puts ""

puts [type constr Sz]
puts [type full Sz]
puts ""

puts [type constr T]
puts [type full {T#(t1,t2)}]
puts [type full {T#(bit,int)}]
puts ""

puts [type constr Bar]
puts [type full Bar]
puts ""

puts [type constr Baz]
puts [type full {Baz#(x,sz)}]
puts [type full {Baz#(Bool,2)}]
puts ""

puts [type constr TopIFC]
puts [type full {TopIFC#(ty)}]
puts [type full {TopIFC#(Bit#(8))}]
puts ""

puts [type constr SubIFC]
puts [type full {SubIFC#(ty)}]
puts [type full {SubIFC#(Bit#(8))}]
puts ""

puts [type constr IfcWithVec]
puts [type full IfcWithVec]
puts ""

puts [type constr U]
puts [type full {U#(t)}]
puts [type full {U#(Bool)}]
puts ""

puts [type constr U2]
puts [type full {U#(t)}]
puts [type full {U#(bit)}]
puts ""

puts [type constr Foo]
puts [type full {Foo#(x)}]
puts [type full {Foo#(int)}]
puts ""

# ---------------
# Typeclasses

# Primitive inserted by the compiler
#
puts [type constr Add]
pprint_type_full [type full {Add#(x,y,z)}]
# XXX we don't yet print specific info based on the type args
# XXX but go ahead and test it, for when we do
# dependency should figure out 'z'
pprint_type_full [type full {Add#(1,2,z)}]
# has an instance
pprint_type_full [type full {Add#(1,2,3)}]
# doesn't have an instance
pprint_type_full [type full {Add#(1,2,4)}]
puts ""

# Primitives in the Prelude
#

# With superclass
puts [type constr Arith]
pprint_type_full [type full {Arith#(x)}]
puts ""

# With dependency (and coherent)
puts [type constr Bits]
pprint_type_full [type full {Bits#(x,szx)}]
# XXX we don't yet print specific info based on the type args
# XXX but go ahead and test it, for when we do
# dependency should figure out 'bsz'
pprint_type_full [type full {Bits#(Bool,bsz)}]
# has an instance
pprint_type_full [type full {Bits#(Bool,1)}]
# doesn't have an instance
pprint_type_full [type full {Bits#(Bool,2)}]
puts ""

# Incoherent
puts [type constr Has_tpl_1]
pprint_type_full [type full {Has_tpl_1#(x,y)}]
puts ""

# XXX We could test user-defined typeclasses and instances here

# ---------------

puts "Bitify Baz (int, n):"
utils::ldisplay  [type bitify {Baz#(int,n)}]
puts "Bitify Baz (int, 5):"
utils::ldisplay  [type bitify {Baz#(int,5)}]
puts "Bitify Baz (Bool, 42):"
utils::ldisplay [type bitify {Baz#(Bool,42)}]

puts "Bitify Baz (BarSet, 12):" 
utils::ldisplay [type bitify {Baz#(BarSet,12)}]

puts "Bitify Vector of Baz (BarSet, 12):"
utils::ldisplay  [type bitify {Vector#(5,Baz#(BarSet,12))}]

puts "Bitify FOO:"
utils::ldisplay [type bitify {Foo#(int)}]

puts "Bitify U2:"
utils::ldisplay  [type bitify {U2#(int)}]


puts "Bitify Tuple:"
utils::ldisplay  [type bitify {T#(int,int)}]
utils::ldisplay  [type bitify {Tuple2#(int,int)}]

puts ""

# ---------------

puts [bpackage load TaggedUnionPoly]

puts [type full NSRK#(n,s,r,k)]

puts ""

# ---------------
