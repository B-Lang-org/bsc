proc test_ovl { topmod vlib } {
    global vtest

    if {$vtest == 1} {
	compile_verilog_pass $topmod.bsv $topmod

	set defines "-D OVL_VERILOG=1 -D OVL_ASSERT_ON=1"
	set includes "-vsearch +:../std_ovl"
	# XXX BSC doesn't recognize vlib as a valid extension
	# XXX so we have to tell BSC to just pass it directly
	set objects "-Xv ../std_ovl/$vlib"
	link_verilog_pass {} $topmod "$defines $includes $objects"

	sim_verilog $topmod {}
	compare_file $topmod.out $topmod.out.expected
    }
}
