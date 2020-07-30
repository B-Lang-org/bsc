#!/bin/csh
# script for generating a list of exp files in particular directories
# expected output format is 
# scheduler.list = disjoint scheduler rulesort

echo "# automatically generated file -- DO NOT EDIT " 
foreach name (bsc.* )
    set dir = `echo $name | cut -c5- `
    set files = `ls -R $name | grep '.exp$' | cut -d. -f1 `
    echo $dir.list = $files 
end

# Add list definitions for 2nd level subdirectories
# targets are not bsc.interra/rtl_quality.group
foreach name (bsc.*/*/ )
    set dir = `echo $name | cut -d/ -f1-2` 
    set files = `ls -R $name | grep '.exp$' | cut -d. -f1 `
    echo $dir.list = $files 
end


set allexpfiles =  `ls -R bsc.* |  grep '.exp$' | cut -d. -f1`
echo ALL.list = $allexpfiles 

set long = ($*)
echo LONG.list = $long

set devlist = ()
foreach aname ($allexpfiles)
    set outname = $aname
    foreach lname ($long)
        if ($aname == $lname) then
            set outname = ""
        endif
    end
    set devlist = ($devlist $outname)
end

echo dev.list = $devlist
