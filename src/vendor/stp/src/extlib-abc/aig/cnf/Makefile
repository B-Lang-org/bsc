SRCTOP = ../../..
include $(SRCTOP)/Makefile.common

SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
CFLAGS += -I..
CXXFLAGS += -I..

libabc.a: 	$(OBJS) 
		$(AR) rc $@ $(OBJS)
		$(RANLIB) $@
	

.PHONY: clean
clean:	
		rm -rf *.o *~ *.a .#* depend

#depend: $(SRCS)
#	@$(CXX) -MM -MG $(CXXFLAGS) $(SRCS) > $@

-include depend		
