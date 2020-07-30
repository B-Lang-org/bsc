
# Pretty print a type analysis result
proc pprint_type_full { res {indent_amt 4} } {
    # tags that we want to indent
    set tags [list superclasses dependencies members instances]

    # the first element is a header
    set is_first 1
    foreach elem $res {
	if { $is_first == 1 } {
	    set is_first 0
	    puts $elem
	} else {
	    pprint_tagged_list_helper $tags $indent_amt $elem $indent_amt
	}
    }
}

# Add more pprint functions here, for other bluetcl command results

# -------------------------

proc pprint_tagged_list_helper { tags indent_amt lst indent } {
    do_indent $indent
    if { [is_tagged_list $tags $lst] == 1 } {
	# if the tagged list is empty
	if { [llength [lindex $lst 1]] == 0 } {
	    puts -nonewline [lindex $lst 0]
	    puts " \{\}"
	} else {
	    puts [lindex $lst 0]
	    foreach elem [lindex $lst 1] {
		pprint_tagged_list_helper \
		    $tags \
		    $indent_amt \
		    $elem \
		    [expr $indent + $indent_amt]
	    }
	}
    } elseif { ([llength $lst] == 0) && ($is_top == 0) } {
	# make sure that sublists don't appear as empty lines
	puts "{}"
    } else {
	puts $lst
    }
}

proc is_tagged_list { tags lst } {
    # We could also indent lists whose first element is the tag,
    # but for now we just indent a list of a tag and a list
    if { [llength $lst] != 2 } {
	return 0
    } else {
	set tag [lindex $lst 0]
	#if { [regexp {^[a-z][a-z]*$} [string tolower $tag]] == 1 }
	if { [string is alnum $tag] } {
	    # We could always accept alphanum strings, but for now
	    # we play it safe by looking for the tag in a given list
	    if { [lsearch -exact $tags $tag] != -1 } {
		return 1;
	    } else {
		return 0;
	    }
	} else {
	    return 0
	}
    }
}

proc do_indent { indent } {
    while { $indent > 0 } {
	puts -nonewline " "
	set indent [expr $indent - 1]
    }
}

# -------------------------

