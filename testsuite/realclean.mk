# add the realclean target here
# to work around makefiles that want suite features, but define realclean

.PHONY: realclean
realclean: localclean
	-@rm -rf bsc.log bsc.log.* *~
	-@$(foreach dir, $(SUBDIRS), \
		$(MAKE) -k -C $(dir) realclean || echo $(CURDIR)/$(dir) ; )
