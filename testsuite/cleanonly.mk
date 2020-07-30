# include file to do make clean
# very gnu-make-specific
.PHONY:	clean
.PHONY:	localclean

KEEPFILES ?= XXXX
DONTKEEPFILES ?= xxxx

TRYDELFILES = $(wildcard \
	*.bi \
	*.bo \
	*.ba \
	*inline-reg \
	*c_sim \
	*.c \
	*.o \
	*.h \
	*.cxx \
	*.so \
	*.filtered \
	*.sorted \
	*.atsexpand \
	*.info \
	*.use \
	*.vcd \
	*.vcs \
	*.cdf \
	*-out \
	*.out \
	*.v \
	*.final-state \
	sys* \
	mk* \
	directc_* \
	*.cexe \
	*.vexe \
	*.syscexe \
	*.prof \
	*.tix \
	*.log \
	*.sum \
	done \
	csrc \
	simv \
	cvcsim \
	*.dump \
	*.daidir \
	*.fsdb \
	*.epp \
	*.pexe \
	*.uexe \
	*.bpp \
	*.sched \
	debussy.rc \
	INCA_libs \
	INCA_libs_* \
	nWaveLog \
	vfastLog \
	*out.raw \
	client_server.cmds \
	*.dSYM \
	work_*/ \
	transcript \
)

DELFILES = $(filter-out \
	%* \
        *% \
        %expected \
        %.sh* \
        %.handbuilt \
        %.ses \
        %testbench.v \
        %.exp \
        design.v \
        $(KEEPFILES), \
        $(TRYDELFILES) \
) $(DONTKEEPFILES)

.PHONY: localclean
localclean:
	@if [ -e bsc.log ] ; then \
		echo "saving bsc.log" ;	\
		mv bsc.log bsc.log.`date +"%F-%R"` ;\
	fi
	@if [ "X$(DELFILES)" != "X" ] ; then \
	echo "cleaning $$PWD" ; \
	rm -rf $(DELFILES) ; fi

.PHONY: rclean
rclean:
	-@$(foreach dir, $(SUBDIRS), \
		$(MAKE) -k TEST_OSTYPE=$(TEST_OSTYPE) -C $(dir) clean || echo $(CURDIR)/$(dir) ; )

.PHONY: clean
clean:	localclean rclean
