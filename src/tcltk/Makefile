
DIRLIST = HaskellTcl

.PHONY: all install
all install: $(DIRLIST)

.PHONY: $(DIRLIST)
$(DIRLIST):
	$(MAKE) -C $@ install

.PHONY: clean full_clean
clean full_clean:
	$(foreach dir, $(DIRLIST), \
		$(MAKE) -C $(dir) $@ ; )
