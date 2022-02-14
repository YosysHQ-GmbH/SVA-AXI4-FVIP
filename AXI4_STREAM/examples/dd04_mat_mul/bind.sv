`default_nettype none

`define VERIFY_SINK 0
`define VERIFY_SOURCE 1

// Sink
bind mat_mul amba_axi4_stream
  #(.BUS_TYPE(`VERIFY_SINK))
sink_checker 
  (.ACLK(s00_axi_aclk),
   .ARESETn(s00_axi_aresetn),
   .TDATA(s00_axis_tdata),
   .TSTRB(1'b1),
   .TKEEP(1'b1),
   .TLAST(s00_axis_tlast),   
   .TID(1'b0),   
   .TDEST(1'b0),
   .TUSER(1'b0),
   .TVALID(s00_axis_tvalid),  
   .TREADY(s00_axis_tready));

// Source
bind mat_mul amba_axi4_stream
  #(.BUS_TYPE(`VERIFY_SOURCE))
source_checker 
  (.ACLK(s00_axi_aclk),
   .ARESETn(s00_axi_aresetn),
   .TDATA(m00_axis_tdata),
   .TSTRB(1'b1),
   .TKEEP(1'b1),
   .TLAST(m00_axis_tlast),
   .TID(1'b0),
   .TDEST(1'b0),
   .TUSER(1'b0),
   .TVALID(m00_axis_tvalid),
   .TREADY(m00_axis_tready));

`undef VERIFY_SINK
`undef VERIFY_SOURCE
