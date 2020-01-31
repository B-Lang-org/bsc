package require Bluetcl 
namespace eval ::Bluesim {

    namespace export \
        sim \
        help 

    # import and re-export the sim and help commands
    namespace import ::Bluetcl::sim
    namespace import ::Bluetcl::help


}

package provide Bluesim 1.0 
