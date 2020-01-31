#
# itk.tcl
# ----------------------------------------------------------------------
# Invoked automatically upon startup to customize the interpreter
# for [incr Tk].
# ----------------------------------------------------------------------
#   AUTHOR:  Michael J. McLennan
#            Bell Labs Innovations for Lucent Technologies
#            mmclennan@lucent.com
#            http://www.tcltk.com/itcl
#
#      RCS:  $Id: itk.tcl,v 1.3 2002/05/14 22:53:28 davygrvy Exp $
# ----------------------------------------------------------------------
#            Copyright (c) 1993-1998  Lucent Technologies, Inc.
# ======================================================================
# See the file "license.terms" for information on usage and
# redistribution of this file, and for a DISCLAIMER OF ALL WARRANTIES.

#
# Provide transparent access to all [incr Tk] commands
#
if {$tcl_platform(os) == "MacOS"} {
    source -rsrc itk:tclIndex
} else {
    lappend auto_path ${itk::library}
}

# ----------------------------------------------------------------------
#  USAGE:  itk::remove_destroy_hook <widget>
#
#  Used internally via "itk_component delete" when disconnecting a
#  component <widget> from the mega-widget that contains it.
#  Each component has a special binding for the <Destroy> event
#  that causes it to disconnect itself from its parent when destroyed.
#  This procedure removes the binding from the binding tag list and
#  deletes the binding.  It is much easier to implement this in
#  Tcl than C.
# ----------------------------------------------------------------------
proc ::itk::remove_destroy_hook {widget} {
    if {![winfo exists $widget]} {return}
    set tags [bindtags $widget]
    set i [lsearch $tags "itk-destroy-$widget"]
    if {$i >= 0} {
        bindtags $widget [lreplace $tags $i $i]
    }
    bind itk-destroy-$widget <Destroy> {}
}

#
# Define "usual" option-handling code for the Tk widgets:
#
itk::usual Button {
    keep -background -cursor -foreground -font
    keep -activebackground -activeforeground -disabledforeground
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Canvas {
    keep -background -cursor
    keep -insertbackground -insertborderwidth -insertwidth
    keep -insertontime -insertofftime
    keep -selectbackground -selectborderwidth -selectforeground
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Checkbutton {
    keep -background -cursor -foreground -font
    keep -activebackground -activeforeground -disabledforeground
    keep -selectcolor
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Entry {
    keep -background -cursor -foreground -font
    keep -insertbackground -insertborderwidth -insertwidth
    keep -insertontime -insertofftime
    keep -selectbackground -selectborderwidth -selectforeground
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Frame {
    keep -background -cursor
}

itk::usual Label {
    keep -background -cursor -foreground -font
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Listbox {
    keep -background -cursor -foreground -font
    keep -selectbackground -selectborderwidth -selectforeground
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Menu {
    keep -background -cursor -foreground -font
    keep -activebackground -activeforeground -disabledforeground
    keep -selectcolor -tearoff
}

itk::usual Menubutton {
    keep -background -cursor -foreground -font
    keep -activebackground -activeforeground -disabledforeground
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Message {
    keep -background -cursor -foreground -font
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Radiobutton {
    keep -background -cursor -foreground -font
    keep -activebackground -activeforeground -disabledforeground
    keep -selectcolor
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Scale {
    keep -background -cursor -foreground -font -troughcolor
    keep -activebackground
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Scrollbar {
    keep -background -cursor -troughcolor
    keep -activebackground -activerelief
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Text {
    keep -background -cursor -foreground -font
    keep -insertbackground -insertborderwidth -insertwidth
    keep -insertontime -insertofftime
    keep -selectbackground -selectborderwidth -selectforeground
    keep -highlightcolor -highlightthickness
    rename -highlightbackground -background background Background
}

itk::usual Toplevel {
    keep -background -cursor
}
