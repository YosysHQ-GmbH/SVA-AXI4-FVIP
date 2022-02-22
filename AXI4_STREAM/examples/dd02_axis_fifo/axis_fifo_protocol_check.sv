`default_nettype none

`define VERIFY_SINK 0
`define VERIFY_SOURCE 1

// Sink
bind axis_fifo amba_axi4_stream
  #(.BUS_TYPE(`VERIFY_SINK),
    .OPT_RESET(1))
sink_checker 
  (.ACLK(clk),    
   .ARESETn(!rst), 
   .TDATA(s_axis_tdata),   
   .TSTRB(1'b0),   
   .TKEEP(s_axis_tkeep),   
   .TLAST(s_axis_last),   
   .TID(s_axis_tid),     
   .TDEST(s_axis_tdest),   
   .TUSER(s_axis_tuser),   
   .TVALID(s_axis_tvalid),  
   .TREADY(s_axis_tready));

// Source
bind axis_fifo amba_axi4_stream
  #(.BUS_TYPE(`VERIFY_SOURCE),
    .OPT_RESET(1))
source_checker 
  (.ACLK(clk),    
   .ARESETn(!rst), 
   .TDATA(m_axis_tdata),   
   .TSTRB(1'b0),
   .TKEEP(m_axis_tkeep),
   .TLAST(m_axis_last),   
   .TID(m_axis_tid),     
   .TDEST(m_axis_tdest),   
   .TUSER(m_axis_tuser),   
   .TVALID(m_axis_tvalid),  
   .TREADY(m_axis_tready));

`undef VERIFY_SINK
`undef VERIFY_SOURCE
