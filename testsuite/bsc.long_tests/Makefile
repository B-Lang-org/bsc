# for "make clean" to work everywhere

CONFDIR = $(realpath ..)

### 
DONTKEEPFILES = 

.PHONY: default
default:
	@echo
	@echo  "Targets are: "
	@echo  " all:        enables all long-running tests"
	@echo  " check:      runs all currently enabled tests"
	@echo  " clean:      cleans all subdirectories"
	@echo  " disable:    disables all long-running tests"
	@echo  " realclean:  removes test output files"
	@echo  " show:       show currently enabled tests"
	@echo 
	@echo Typical usage to run just one test
	@echo "  make <dir>"  ## only need to do once
	@echo "  make check"
	@echo 
	@echo To disable a single test
	@echo "  make no-<dir>"
	@echo 
	@echo Directory targets are: $(DIRS)
	@echo 

.PHONY: checknote
checknote: 
	@echo "Makefile target check runs only currently enabled tests"

CHECKPREREQUISITES += checknote

.PHONY: localchecknote
localchecknote: 
	@echo "Makefile target localcheck runs only currently enabled tests"

LOCALCHECKPREREQUISITES += localchecknote

### MPEG4 #######################################
DIRS += MPEG4 
.PHONY: MPEG4 no-MPEG4
MPEG4:
	ln -sf mpeg.exp.golden MPEG4/mpeg.exp
no-MPEG4:
	@rm MPEG4/mpeg.exp
### ###############################################

### conflict_free_large #######################################
DIRS += conflict_free_large 
.PHONY: conflict_free_large no-conflict_free_large
conflict_free_large:
	ln -sf conflict_free_large.exp.golden conflict_free_large/conflict_free_large.exp
no-conflict_free_large:
	@rm conflict_free_large/conflict_free_large.exp


### log2_loop #######################################
DIRS += log2_loop
.PHONY: log2_loop no-log2_loop
log2_loop:
	ln -sf log2_loop.exp.golden log2_loop/actionvalue/log2_loop.exp
	ln -sf log2_loop.exp.golden log2_loop/module/log2_loop.exp
	ln -sf log2_loop.exp.golden log2_loop/pure/log2_loop.exp
no-log2_loop:
	@rm log2_loop/actionvalue/log2_loop.exp
	@rm log2_loop/module/log2_loop.exp
	@rm log2_loop/pure/log2_loop.exp

### ###############################################

#### To add a testcase do the following:
#### 1)  Add a make target for the specific directory.  See the common
####     6-line examples above.
#### 2)  Add the necessary .exp.golden files and .expected files to the
####     directory.  Be sure to include both Bluesim and Verilog cases
####     where applicable.

####  Note that the *.exp.golden file should be checked into SVN, and
####  the *.exp file is merely a link created and managed by the this
####  Makefile.  The links will be removed by a "make disable".

## Enable all the long running tests
.PHONY:	all
all:	$(DIRS)

## Show currently enabled tests
ENABLED = $(shell for d in $(DIRS); do if [ -f $$d/*.exp ]; then echo $$d; fi; done)

.PHONY: show
show:
	@echo "Currently enabled test directories:"
	@echo "  $(ENABLED)"

## disable all of the tests
.PHONY: disable
disable: $(addprefix no-,$(DIRS))

## clean up test-related files
realclean:
	@rm -rf *.log *.sum

#### This must be at the end ##############################
include $(CONFDIR)/norealclean.mk

