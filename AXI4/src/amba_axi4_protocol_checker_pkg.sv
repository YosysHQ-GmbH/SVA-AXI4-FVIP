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
 */
`ifndef __AMBA_AXI4_PROTOCOL_CHECKER_PKG__
 `define __AMBA_AXI4_PROTOCOL_CHECKER_PKG__
package amba_axi4_protocol_checker_pkg;
   /* This was originally described as an user defined
    * enum, but to avoid type casting for designs that
    * does not use the same type for BRESP and RRESP,
    * it's better to express this as old-style params. */
   localparam logic [1:0] OKAY   = 2'b00,
			  EXOKAY = 2'b01,
			  SLVERR = 2'b10,
			  DECERR = 2'b11;

   // AxLOCK values
   localparam logic [0:0] NORMAL    = 1'b0,
			  EXCLUSIVE = 1'b1;

   /* Burst len encoding for all transfers
    * except BURST = INCR (A3-46) */
   localparam logic [3:0] BURSTLEN1  = 4'h0;
   localparam logic [3:0] BURSTLEN2  = 4'h1;
   localparam logic [3:0] BURSTLEN3  = 4'h2;
   localparam logic [3:0] BURSTLEN4  = 4'h3;
   localparam logic [3:0] BURSTLEN5  = 4'h4;
   localparam logic [3:0] BURSTLEN6  = 4'h5;
   localparam logic [3:0] BURSTLEN7  = 4'h6;
   localparam logic [3:0] BURSTLEN8  = 4'h7;
   localparam logic [3:0] BURSTLEN9  = 4'h8;
   localparam logic [3:0] BURSTLEN10 = 4'h9;
   localparam logic [3:0] BURSTLEN11 = 4'hA;
   localparam logic [3:0] BURSTLEN12 = 4'hB;
   localparam logic [3:0] BURSTLEN13 = 4'hC;
   localparam logic [3:0] BURSTLEN14 = 4'hD;
   localparam logic [3:0] BURSTLEN15 = 4'hE;
   localparam logic [3:0] BURSTLEN16 = 4'hF;

   /* Burst type encoding, see pA3-48
    * Table A3-3 */
   localparam logic [1:0] FIXED = 2'b00,
			  INCR  = 2'b01,
			  WRAP  = 2'b10,
			  RESERVED = 2'b11;

   /* AxSIZE related parameters, see
    * Table A3-2 Burst size encoding */
   localparam logic [2:0] SIZE1B   = 3'b000,
			  SIZE2B   = 3'b001,
			  SIZE4B   = 3'b010,
			  SIZE8B   = 3'b011,
			  SIZE16B  = 3'b100,
			  SIZE32B  = 3'b101,
			  SIZE64B  = 3'b110,
			  SIZE128B = 3'b111;

   /* The AXI VIP can  be configured in the four different
    * types of agents listed below. */
   typedef enum logic [1:0] {SOURCE      = 2'b00,
			     DESTINATION = 2'b01,
			     MONITOR     = 2'b10,
			     CONSTRAINT  = 2'b11} axi4_agent_t;

   /* To configure the VIP to check either AXI4 Full
    * or AXI4 lite (the set of properties are different,
    * being AXI4 Full more complicated than AXI4 Lite). */
   typedef enum logic [0:0] {AXI4LITE = 1'b0,
			     AXI4FULL = 1'b1} axi4_types_t;

   typedef struct packed {
      /* AXI4 Port Related Settings */
      // The ID (tag) width of the DUT, to track order of transactions
      int unsigned ID_WIDTH;
      // The address width of the DUT
      int unsigned ADDRESS_WIDTH;
      // The data width of the DUT
      int unsigned DATA_WIDTH;
      // The sideband width of the DUT
      int unsigned AWUSER_WIDTH;
      int unsigned WUSER_WIDTH;
      int unsigned BUSER_WIDTH;
      int unsigned ARUSER_WIDTH;
      int unsigned RUSER_WIDTH;
      /* AXI4 Protocol Checker Configuration */
      // The number of write transactions the formal IP should monitor
      int unsigned MAX_WR_BURSTS;
      // The number of read transactions the formal IP should monitor
      int unsigned MAX_RD_BURSTS;
      // The write burst len the formal IP will use to monitor transactions
      int unsigned MAX_WR_LENGTH;
      // The write burst len the formal IP will use to monitor transactions
      int unsigned MAX_RD_LENGTH;
      // Max number of cycles a source can wait for a destination to ack
      // the transaction
      int unsigned MAXWAIT;
      // To define what agent will be verified (src, dst, mon, cons)
      axi4_agent_t VERIFY_AGENT_TYPE;
      // To define if the protocol to verify is AXI4LITE or AXI4FULL
      axi4_types_t PROTOCOL_TYPE;
      // Enable single interface requirements properties
      bit          INTERFACE_REQS;
      // To define if cover properties will be enabled: recommended = yes
      bit	   ENABLE_COVER;
      // To define if the formal IP should verify invalid states
      // (X-prop), recommended = yes
      bit          ENABLE_XPROP;
      // To define if the formal IP should look for deadlocks
      // (using MAXWAIT parameter), recommended = yes.
      bit	   ARM_RECOMMENDED;
      // To define if the formal IP should check that the parameters of the
      // IP are set correctly, recommended = yes.
      bit	   CHECK_PARAMETERS;
      // To define if the transactions uses the STRB signal, recommended =
      // depends on the user IP features.
      bit          OPTIONAL_WSTRB;
      // To define if the transactions are masked (1) or unmasked (0)
      // recommended = depends on the user IP features.
      bit          FULL_WR_STRB;
      // To define if the formal IP should verify correct values after reset,
      // recommended = yes.
      bit	   OPTIONAL_RESET;
      // To define if the formal IP should verify exclusive transactions,
      // recommended = yes, definetely, if the user IP supports it.
      bit 	   EXCLUSIVE_ACCESS;
   } axi4_checker_params_t;
endpackage // amba_axi4_protocol_checker_pkg
`endif
