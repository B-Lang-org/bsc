package DQueueConfig;

// This package contains configuration parameters.

// First come the various field sizes.  Note that in BSV these parameters are
// types (we call them "numeric types"), so that by the time the design
// typechecks we can be confident all the bit sizes match up.

typedef  8 CS_SIZE;
typedef 16 ROW_SIZE;
typedef 10 BANK_SIZE;

typedef  9 COL_SIZE;
typedef  3 B_SIZE;

typedef 14 LENGTH_SIZE;
typedef  1 WRAP_SIZE;
typedef  1 RW_SIZE;
typedef 16 PRIORITY_SIZE;
typedef 12 SOURCE_ID_SIZE;
typedef 11 BUFF_ID_SIZE;

// This is one of the various possible ways of specifying how cs, row and bank
// are to be packed into a page address.  cs=1, row=2, bank=3; so 123
// specifies the order (cs,row,bank), 312 specifies (bank,cs,row), and so on.

Integer page_packing = 132;

Bool pipelining = True;

// The number of slots provided in the queue module.

Integer queue_length = 4;

endpackage
