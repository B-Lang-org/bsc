# Tcl package index file, version 1.1

if {![package vsatisfies [package provide Tcl] 8.4]} {return}
package ifneeded http 2.7.1 [list tclPkgSetup $dir http 2.7.1 {{http.tcl source {::http::config ::http::formatQuery ::http::geturl ::http::reset ::http::wait ::http::register ::http::unregister ::http::mapReply}}}]
