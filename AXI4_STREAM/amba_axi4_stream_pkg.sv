/*  AXI Formal Verification IP 2.0.
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
`ifndef __AMBA_AXI4_STREAM_PKG__
 `define __AMBA_AXI4_STREAM_PKG__

/* The Symbiotic EDA AXI Verification IP is configured using
 * the following parameters:
 *       A) AXI4_STREAM_AXI_BUS_TYPE: 
 *          When set to 0 acts as sink component.
 *          When set to 1 acts as source component.
 *       B) AXI4_STREAM_DATA_WIDTH_BYTES: 
 *          The size of the data bus in BYTES.
 *       C) AXI4_STREAM_DEST_WIDTH:
 *          The size of TDEST in BITS.
 *       D) AXI4_STREAM_ID_WIDTH:
 *          The size of TID in BITS.
 *       E) AXI4_STREAM_USER_WIDTH:
 *          The size of TUSER in BITS.
 *       F) AXI4_STREAM_GEN_WITNESS:
 *          Generate witness traces (intended for RTL bring-up only).
 *       G) AXI4_STREAM_ARM_RECOMMENDED:
 *          Enable recommended TREADY/TVALID MAXWAIT rule.
 *       H) AXI4_STREAM_MAXWAITS:
 *          Configure max clock cycles within a 
 *          TVALID-TREADY handshake.
 *       I) AXI4_STREAM_CHECK_SETUP:
 *          Verify simple properties that demonstrate correct
 *          configuration of the AXI VIP.
 *       J) AXI4_STREAM_RESET_CHECKS:
 *          Enable/disable ARESETn checks.
 *          Set this parameter to 0 if the reset port does
 *          not control the AXI4-Stream interface.
 *       K) AXI$_STREAM_RESET_SIM:
 *          Most of the properties listed in this VIP have a
 *          default disable clause (reset state). Setting this
 *          parameter to 1 enables TVALID check during reset
 *          in a simulation environment (not formal).
 *       L) AXI4_STREAM_CHECK_XPROP:
 *          Run X-propagation checks with formal, on some
 *          control and data AXI-Stream ports.
 */

package amba_axi4_stream_pkg;
   
   localparam AXI4_STREAM_BUS_TYPE         =  1;
   localparam AXI4_STREAM_DATA_WIDTH_BYTES =  2; 
   localparam AXI4_STREAM_DEST_WIDTH       =  0;
   localparam AXI4_STREAM_ID_WIDTH	   =  0;
   localparam AXI4_STREAM_USER_WIDTH       =  0;
   localparam AXI4_STREAM_GEN_WITNESS      =  0; 
   localparam AXI4_STREAM_ARM_RECOMMENDED  =  1;
   localparam AXI4_STREAM_MAXWAITS	   = 16;
   localparam AXI4_STREAM_CHECK_SETUP      =  1;
   localparam AXI4_STREAM_RESET_CHECKS     =  1;
   localparam AXI4_STREAM_RESET_SIM        =  0;
   localparam AXI4_STREAM_CHECK_XPROP      =  0;
   // For X-prop rules (not supported by Tabby CAD yet)
   localparam ENABLED_XPROP = 0;
   
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Port config (not expecting any user edits)           *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   localparam DATA_WIDTH_MAX  = ((AXI4_STREAM_DATA_WIDTH_BYTES) ? (8*(AXI4_STREAM_DATA_WIDTH_BYTES) - 1) : 0);
   localparam DEST_WIDTH_MAX  = ((AXI4_STREAM_DEST_WIDTH) ? ((AXI4_STREAM_DEST_WIDTH) - 1) : 0);
   localparam STRB_WIDTH      = AXI4_STREAM_DATA_WIDTH_BYTES;
   localparam STRB_WIDTH_MAX  = ((STRB_WIDTH) ? ((STRB_WIDTH) - 1) : 0);
   localparam KEEP_WIDTH_MAX  = ((STRB_WIDTH) ? ((STRB_WIDTH) - 1) : 0);
   localparam ID_WIDTH_MAX    = ((AXI4_STREAM_ID_WIDTH) ? ((AXI4_STREAM_ID_WIDTH) - 1) : 0);
   localparam USER_WIDTH_MAX  = ((AXI4_STREAM_USER_WIDTH) ? ((AXI4_STREAM_USER_WIDTH) - 1) : 0);
   localparam ONE_BIT_WIDTH   = 0;
   
   typedef logic [ONE_BIT_WIDTH	  : 0] axi4s_aclk;
   typedef logic [ONE_BIT_WIDTH	  : 0] axi4s_aresetn;
   typedef logic [DATA_WIDTH_MAX  : 0] axi4s_data;
   typedef logic [STRB_WIDTH_MAX  : 0] axi4s_strb;
   typedef logic [KEEP_WIDTH_MAX  : 0] axi4s_keep;
   typedef logic [ONE_BIT_WIDTH	  : 0] axi4s_last;
   typedef logic [ID_WIDTH_MAX	  : 0] axi4s_id;
   typedef logic [DEST_WIDTH_MAX  : 0] axi4s_dest;
   typedef logic [USER_WIDTH_MAX  : 0] axi4s_user;
   typedef logic [ONE_BIT_WIDTH	  : 0] axi4s_valid;
   typedef logic [ONE_BIT_WIDTH	  : 0] axi4s_ready;
   
endpackage // amba_axi4_stream_pkg
`endif

