# AXI4-Stream FIFO

This design is from Alex Forencich’s [repo](https://github.com/alexforencich/verilog-axis/blob/master/rtl/axis_fifo.v).

Issues found by `AMBA AXI4 Stream Protocol Checker`:

Sink:

| **Assertion** | **Information** | **Offending code** |
| --- | --- | --- |
| assert\_VIP\_max\_size\_of_tdest | The recommended max size of TDEST is 4-bits (Ref: 2.1 Signal List, p2-2, Table 2-1). | axis_fifo.v:53-54<br><br>// tdest signal width<br><br> parameter DEST_WIDTH = 8 |
| assert\_SNK\_TREADY_MAXWAIT | TREADY should be asserted within MAXWAITS cycles of TVALID being asserted. | Possible wrong number of cycles defined in amba\_axi4\_stream\_pkg.sv:68<br><br>localparam AXI4\_STREAM\_MAXWAITS  = 16;<br><br>Or possible deadlock (needs debug). |
| cover\_DATA\_BYTE | Data Byte: The associated byte contains valid information that must be transmitted between source and destination (Ref: 2.4.3 TKEEP and TSTRB combinations, p2-9, Table 2-2). | Unreachable cover in amba\_axi4\_stream.sv:670 |

Source:

| **Assertion** | **Information** | **Offending code** |
| --- | --- | --- |
| assert\_VIP\_max\_size\_of_tdest | The recommended max size of TDEST is 4-bits (Ref: 2.1 Signal List, p2-2, Table 2-1). | axis_fifo.v:53-54<br><br>// tdest signal width<br><br> parameter DEST_WIDTH = 8 |
| assert\_SRC\_STABLE_TLAST | Once the master has asserted TVALID, data and control information from master must remain stable \[TLAST\] (2.2.1, p2-3, Figure 2-1). | Undriver tlast in axis_fifo.v. |
| assert\_SRC\_EXIT_RESET | VALID must be low for the first clock edge that ARESETn goes high (2.7.2 Reset, p2-11, Figure 2-4). | The rst pin does not intervene in the AXI4-Stream interface. |
| cover\_DATA\_BYTE | Data Byte: The associated byte contains valid information that must be transmitted between source and destination, 2.4.3 TKEEP and TSTRB combinations, p2-9, Table 2-2. | Unreachable cover in amba\_axi4\_stream.sv:670 |
| cover\_NULL\_BYTE | Null Byte: The associated byte does not contain information and can be removed from the stream, Ref: 2.4.3 TKEEP and TSTRB combinations, p2-9, Table 2-2. | Unreachable cover in amba\_axi4\_stream.sv:672 |

## Challenge
Fix the implementation so all properties are proven.
