Overview:

This directory contains a Bluespec example of a AMBA bus modeled at
the transaction level.  These models are useful for development and
analysis of different AMBA bus architectures, since their interconnect
can be easily reconfigured, and the models provide a wide range of
performance behavior options.

Understanding the models.

The AMBA bus model conceptually contain two type of actors -- Masters
and Slaves. Masters initiate bus transactions, while the Slaves response
to the Master's requests.  The AMBA bus provides the necessary
arbitration, decode and muxing logic to support an arbitrary number of
Masters and Slaves.

Interfaces.bsv

From the Bluespec modeling view, each master provide an identical
Master interface which connects to the bus, while each Slave provide a
Slave interface for the bus connection. Specific modules may provide
more than one interface, for example a DMAC acts as a master during
memory transfers, yet requires a slave interface for it configuration.
The specific behavior of Masters and Slaves is not relevant, provided
they meet the interface requirements.  The AMBA bus structure must also
provide interfaces to connect with the masters and slave. For this
model, we define two interfaces, the BusMasterSide and BusSlaveSide to
connect with the Master or Slave side interfaces.   See Interfaces.bsv
for more descriptions of these interfaces.

Slaves.bsv

The slaves are conceptually simple since they respond to requests
from masters.  Three slaves are developed -- a default Slave, a slave
with 1 cycle latency and one with 2 cycle latency, and one with a
runtime configurable values.  All slaves have a Slave type interface,
and thus are plug compatible.

Masters.bsv

The master is a more complicated module since it must generate
requests to send on the bus.   For the generation of requests, a
counter, LFSR, and a FIFO are used.  The counter increments each cycle
to and provide a mechanism to create time stamps.  The LFSR creates
random numbers which are used to trigger different slave addresses.
The FIFO (requestQ) is used to interface the address generation to the
bus control.

The interface methods for the master are in 2 part, the bus request and
grant, and the transaction request and response.  The bus access is
requested when there is data in the request fifo, and the bus grant
is received and sent to the r_granted R-Wire.  RWires are used to
remove clock cycle latency.  When the bus is granted, (regardless if
it was requested) the get method of the m_request sub-interface is
called. This  methods allows the bus to get the request from the fifo,
or an idle transaction. 

When the bus has data to put to the master, the put method of the
m_response sub interface is called. The method displays the response
for all non-idle transactions.

Buses.bsv

The bus modules tie masters and slaves together, via the BusMasterSide
and BusSlaveSide interfaces.  As an example, consider the transaction
flow for the smallest case module bus_1m_1s, which has 1 master, 1
slave, and 1 default slave.  A master requests the bus, triggering
method bms_bus_request and thus sets the RWire busrequest.  The
bms_bus_grant method is triggered, sending the grant signal back to the
master.  The master responds by putting a request to the bms_request
sub-interface (put method). The request is set to an RWire and the
addresses is address is decoded and slaveSelect (RWire) is set.
One of the get slave-side get methods is called which takes
the request from the RWire, and presents it for the slave to get.

The slave  eventually responds, by calling the put method of the
bs_response sub-interface.  This in turn sends the response to the
RWire-response.  The current active BusMasterSide interface
(bms_response) method takes the the response, and presents if for the
Master to get. 

TODO description of mkSlaveIfc



Instrumentation

Transaction model

Some difference of the transaction model versus the AMBA model.
-- In this transactional model, the Master sends both the address and
data in one cycle, whereas the AMBA spec has a separate address and
data phase.
-- The masters nor slaves are set to deal with AMBA transaction type
busy, idle, seq or seq1.  The masters will always send a transaction
if the bus grant is asserted.
