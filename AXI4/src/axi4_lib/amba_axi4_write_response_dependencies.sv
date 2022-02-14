/*  AXI4 Formal Properties.
 *
 *  Copyright (C) 2021  Diego Hernandez <diego@yosyshq.com>
 *  Copyright (C) 2021  Sandia Corporation
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */
`default_nettype none
`ifndef _FORWARD_PROGRESS_SCOREBOARD_PKG_
 `define _FORWARD_PROGRESS_SCOREBOARD_PKG_
package forward_progress_scoreboard_pkg;
   // Configuration knobs
   typedef enum bit [0:0] {NO, YES} knobs_t;
   typedef enum bit [0:0] {ASSUME, GUARANTEE} flow_t;
   typedef enum bit [0:0] {IN_ORDER, OUT_OF_ORDER} checks_t;

   // Default messages for failing properties (helps to interpet and debug the CEX).
 `define no_overflow_err_msg     "Violation: The number of BURSTS is larger than the number of MAX_PENDING requests that the \
                                  scoreboard can allocate. It is suggested to review the parameters of the Formal IP and fix \
                                  any wrong value."
 `define data_integrity_err_msg  "Violation: The destination must wait for AWVALID, AWREADY, to be asserted before asserting \
                                  BVALID. (AXI4 write response dependency, A3-44, Figure A3-7)."
 `define making_progress_err_msg "Violation: A potential deadlock has been found. The transaction counter has reached \
                                  MAX_LATENCY cycles without making progress."

endpackage // forward_progress_scoreboard_pkg
`endif

module forward_progress_scoreboard
  import forward_progress_scoreboard_pkg::*;
  #(parameter int unsigned SYMBOL_WIDTH   = 8,
    parameter int unsigned MAX_PENDING    = 16,
    parameter knobs_t      LATENCY_CHECK  = YES,
    parameter int unsigned MAX_LATENCY    = 16,
    parameter knobs_t      OVERFLOW_CHECK = YES,
    parameter flow_t       AG_FLOW        = ASSUME,
    parameter checks_t     ORDER          = OUT_OF_ORDER,
    parameter knobs_t      COVERS         = YES,
    parameter int unsigned COVER_DATA_N   = MAX_PENDING,
    localparam CNTW = MAX_PENDING < 2 ? 1 : $clog2(MAX_PENDING))
   (input wire in_clk,
    input wire in_rstn,
    input wire in_handshake_valid,
    input wire in_handshake_ready,
    input wire out_handshake_valid,
    input wire out_handshake_ready,
    input wire [SYMBOL_WIDTH-1:0] in_data,
    input wire [SYMBOL_WIDTH-1:0] out_data,
    output logic [CNTW:0] pending_reads);

   logic in_request;
   logic out_response;

   /* The var 'scoreboard_ps' will help us to calculate the
    * pending reads depending on the number of requests and
    * responses events happening so far. */
   logic [CNTW:0] scoreboard_ps = {CNTW{1'b0}};
   logic [CNTW:0] scoreboard_ns;

   /* And the 'data_array_ps' is used to store the 'in_data'
    * information to build data integrity properties. */
   logic [SYMBOL_WIDTH-1:0] data_ps [MAX_PENDING:0] = '{default:0};
   logic [SYMBOL_WIDTH-1:0] data_ns [MAX_PENDING:0];

   logic [CNTW:0] index_value;

      /* SystemVerilog has great built-in methods to work with arrays,
    * but but unfortunately they are not synthesizable:
    * Find first element in the array that matches with given data at input.
    * This function can be easily modified to define the index scan order,
    * from L to R or R to L. */
   function automatic logic [CNTW:0] find_first_synth
     (logic [CNTW:0] pending_counter,
      logic [SYMBOL_WIDTH-1:0] recorded_data [MAX_PENDING:0],
      logic [SYMBOL_WIDTH-1:0] search_value);
      logic [CNTW:0] index;
      index = pending_counter; // select a default value in case observed data value is not found
      /* Then, scan the whole array of recorded values (the iterator value that the 'foreach' construct
       * returns depends on how the unpacked array is defined. */
      foreach(recorded_data[i]) begin
         // is i the lowest index in the array that matches with BID?
         if((i < pending_counter) && (search_value == recorded_data[i])) begin
            // If yes, then we use this position from the array of recorded values
            index = i;
         end
      end
      return index;
   endfunction // find_first_synth

   /* Deallocate the element that has been read due an read response event.
    * This function uses the index returned by `find_first_synth` to position
    * in the array of values and deallocate this specific value by shifting
    * the array. */
   function void shift_array
     (logic [CNTW:0] start_index,
      logic [CNTW:0] end_index);
      if(start_index < end_index) begin
	 for(int i=0; i<MAX_PENDING; i++)
	   if(i >= start_index)
	     data_ns[i] = data_ns[i+1];
      end
   endfunction // shift_array

   // AXI uses async reset
   always_ff @(posedge in_clk, negedge in_rstn)
     begin
	if(!in_rstn) begin
	   scoreboard_ps <= {CNTW{1'b0}};
	   data_ps <= '{default:0};
	end
	else
	  begin
	     scoreboard_ps <= scoreboard_ns;
	     data_ps <= data_ns;
	  end
     end

   always_comb
     begin
	// Default values to avoid infering latches
	data_ns = data_ps;
	scoreboard_ns = scoreboard_ps;

	// Update what happens when important events are fired
	in_request   = in_handshake_valid && in_handshake_ready;
	out_response = out_handshake_valid && out_handshake_ready;

	// Calculate the current index
	index_value = find_first_synth(scoreboard_ps, data_ps, out_data);

	/* When a write request is issued, store the value seen at
	 * in_data in the array of recorded values. */
	if(in_request) data_ns[scoreboard_ps] = in_data;

	/* When a read request is issued, look for the value seen
	 * at out_data in the array of recorded values. The index
	 * value returned by the scan should be less than the
	 * pending reads to be taken as correct. */
	if(out_response) shift_array(index_value, scoreboard_ns);

	// Also, update the scoreboard value.
	scoreboard_ns = scoreboard_ps + in_request - out_response;

	// And propagate debug signals
	pending_reads = scoreboard_ps;
     end // always_comb

   // Formal Properties
   default clocking fpv_clk @(posedge in_clk); endclocking
   default disable iff(!in_rstn);

   generate
      if(AG_FLOW == ASSUME) begin
	 cp_no_overflow_no_dead_end: assume property(scoreboard_ps == MAX_PENDING-1 |-> !in_handshake_valid)
	   else $error(`no_overflow_err_msg);

	 if(ORDER == OUT_OF_ORDER) begin
	    cp_data_integrity_out_of_order: assume property(out_handshake_valid |-> index_value < scoreboard_ps)
	      else $error(`data_integrity_err_msg);
	 end

	 else begin
	    cp_data_integrity_in_order: assume property(out_handshake_valid |-> index_value == {CNTW{1'b0}})
	      else $error(`data_integrity_err_msg);
	 end

	 if(LATENCY_CHECK == YES && !$isunbounded(MAX_LATENCY)) begin
	    cp_making_progress_bounded: assume property(scoreboard_ps <= MAX_LATENCY)
	      else $error(`making_progress_err_msg);
	 end

	 else begin
	    cp_making_progress_unbounded: assume property(in_request && !out_response |=> s_eventually out_response)
	      else $error(`making_progress_err_msg);
	 end
      end
      else if(AG_FLOW == GUARANTEE) begin
	 ap_no_overflow: assert property(in_handshake_valid |-> scoreboard_ps < MAX_PENDING)
	   else $error(`no_overflow_err_msg);

	 if(ORDER == OUT_OF_ORDER) begin
	    ap_data_integrity_out_of_order: assert property(out_handshake_valid |-> index_value < scoreboard_ps)
	      else $error(`data_integrity_err_msg);
	 end

	 else begin
	    ap_data_integrity_in_order: assert property(out_handshake_valid |-> index_value == {CNTW{1'b0}})
	      else $error(`data_integrity_err_msg);
	 end

	 if(LATENCY_CHECK == YES && !$isunbounded(MAX_LATENCY)) begin
	    ap_making_progress_bounded: assert property(scoreboard_ps <= MAX_LATENCY)
	      else $error(`making_progress_err_msg);
	 end

	 else begin
	    ap_making_progress_unbounded: assert property(in_request && !out_response |-> s_eventually out_response)
	      else $error(`making_progress_err_msg);
	 end
      end
   endgenerate

   genvar i, j;
   generate
      if(COVERS == YES) begin: cover_scenarios
	 for(i=1; i<MAX_PENDING-1; i++) begin: symbol_in
	    wp_symbol_in: cover property(in_request && scoreboard_ns == i);
	 end
      end
   endgenerate
   
endmodule // forward_progress_scoreboard

module amba_axi4_write_response_dependencies
  import amba_axi4_protocol_checker_pkg::*;
   #(parameter axi4_checker_params_t cfg =
     '{ID_WIDTH:          4,
       MAX_WR_BURSTS:     4,
       MAX_RD_BURSTS:     4,
       VERIFY_AGENT_TYPE: SOURCE,
       PROTOCOL_TYPE:     AXI4LITE,
       default: '0})
   (input wire ACLK, ARESETn,
    input wire [cfg.ID_WIDTH-1:0] AWID, BID,
    input wire BVALID, BREADY,
    input wire AWVALID, AWREADY,
    input wire WVALID, WREADY, WLAST);

   import forward_progress_scoreboard_pkg::*;

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                 AW scoreboard modeling start                    *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   // The number of recorded AW (i.e., how many AWVALID && AWREADY have happened so far?)
   bit [$clog2(cfg.MAX_WR_BURSTS):0] outstandingAW;

   // Instantiate the forward progress counter for AW
   localparam flow_t RESOLUTION = cfg.VERIFY_AGENT_TYPE inside {MONITOR, DESTINATION} ? GUARANTEE : ASSUME;

   forward_progress_scoreboard
     #(.SYMBOL_WIDTH(cfg.ID_WIDTH),
       .MAX_PENDING(cfg.MAX_WR_BURSTS),
       .LATENCY_CHECK(YES),
       .MAX_LATENCY(16),
       .OVERFLOW_CHECK(YES),
       .AG_FLOW(RESOLUTION),
       .ORDER(OUT_OF_ORDER))
   forward_progress_AW
     (.in_clk(ACLK),
      .in_rstn(ARESETn),
      .in_handshake_valid(AWVALID),
      .in_handshake_ready(AWREADY),
      .out_handshake_valid(BVALID),
      .out_handshake_ready(BREADY),
      .in_data(AWID),
      .out_data(BID),
      .pending_reads(outstandingAW));

   /*            ><><><><><><><><><><><><><><><><><><><><             *
    *                  W scoreboard modeling start                    *
    *            ><><><><><><><><><><><><><><><><><><><><             */
   // The number of recorded AW (i.e., how many AWVALID && AWREADY have happened so far?)
   bit [$clog2(cfg.MAX_WR_BURSTS):0] outstandingW;
endmodule // amba_axi4_write_response_dependencies
`default_nettype wire
