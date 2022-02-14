bind axi_fifo amba_axi4_stream
  #(.BUS_TYPE(0),
    .OPT_RESET(1))
fifo_checker_sink
  (.ACLK(clk),
   .ARESETn(!rst),
   .TDATA(in_data),
   .TSTRB(1'b0),
   .TKEEP(1'b0),
   .TLAST(1'b1),
   .TID(1'b0),
   .TDEST(1'b0),
   .TUSER(1'b0),
   .TVALID(in_valid),
   .TREADY(in_ready));

bind axi_fifo amba_axi4_stream
  #(.BUS_TYPE(1),
    .OPT_RESET(1))
fifo_checker_source
  (.ACLK(clk),
   .ARESETn(!rst),
   .TDATA(out_data),
   .TSTRB(1'b0),
   .TKEEP(1'b0),
   .TLAST(1'b1),
   .TID(1'b0),
   .TDEST(1'b0),
   .TUSER(1'b0),
   .TVALID(out_valid),
   .TREADY(out_ready));
