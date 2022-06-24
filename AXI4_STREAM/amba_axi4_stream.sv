/*  AMBA AXI4 Formal Properties.
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

/*   _______________________________________________________
    /\                                                      \
(O)===)><><><><><><><><><><><><><><><><><><><><><><><><><><><)==(O)
    \/''''''''''''''''''''''''''''''''''''''''''''''''''''''/
    (       ______                                         ( 
     ) (_) |						    )
    (	   |						   ( 
     )	 _ | ABLE OF CONTENTS				    )
	(_/						     
    (							   ( 
     )	   Section I  : Parameters.			    )
    (	   Section II : AXI VIP Configuration Rules.	   ( 
     )	   Section III: Handshake Rules.		    )
           Section IV : ARM Recommended Rules.
    (	   Section V  : X-Prop Rules.			   )  
     )	   Section VI : Data Signaling rules.		  ( 
    (	   Section VII: Auxiliary Logic.	           )
     )							  ( 
    (							   )
     )							  (
    /\''''''''''''''''''''''''''''''''''''''''''''''''''''''\    
(O)===)><><><><><><><><><><><><><><><><><><><><><><><><><><><)==(O)
    \/______________________________________________________/ */


/*		 ><><><><><><><><><><><><><><><><><><><><             *
 *		 Section I: Parameters.                               *
 *		 ><><><><><><><><><><><><><><><><><><><><	      */
/* This AMBA AXI Properties package is configured using
 * the following parameters:
 *       A) BUS_TYPE [default value AXI4_STREAM_BUS_TYPE]: 
 *          When set to 0 acts as sink component.
 *          When set to 1 acts as source component.
 *       B) AXI4_STREAM_DATA_WIDTH_BYTES:
 *          The size of the data bus in BYTES (from the pkg).
 *       C) AXI4_STREAM_DEST_WIDTH:
 *          The size of TDEST in BITS (from the pkg).
 *       D) AXI4_STREAM_ID_WIDTH:
 *          The size of TID in BITS (from the pkg).
 *       E) AXI4_STREAM_USER_WIDTH:
 *          The size of TUSER in BITS (from the pkg).
 *       F) RTL_FLOW [default value AXI4_STREAM_GEN_WITNESS]:
 *          Generate witness traces (intended for RTL bring-up only).
 *       G) ARM_RCMD [default value AXI4_STREAM_ARM_RECOMMENDED]:
 *          Enable recommended TREADY/TVALID MAXWAIT (deadlock) rule.
 *       H) MAXWAITS [default value AXI4_STREAM_MAXWAITS]:
 *          Configure max clock cycles within a 
 *          TVALID-TREADY handshake for potential deadlock check.
 *       I) OPT_SETUP [default value AXI4_STREAM_CHECK_SETUP]:
 *          Verify simple properties that demonstrate correct
 *          configuration of the AXI VIP.
 *       J) OPT_RESET [default value AXI4_STREAM_RESET_CHECKS]:
 *          Enable/disable ARESETn checks.
 *          Set this parameter to 0 if the reset port does
 *          not control the AXI4-Stream interface.
 *       K) RESET_SIM [default value AXI4_STREAM_RESET_SIM]:
 *          Most of the properties listed in this VIP have a
 *          default disable clause (reset state). Setting this
 *          parameter to 1 enables TVALID check during reset
 *          in a simulation environment (not formal).
 *       L) XPROP_EN [default value AXI4_STREAM_CHECK_XPROP]:
 *          Run X-propagation checks with formal, on some
 *          control and data AXI-Stream ports.
 */
`default_nettype none

module amba_axi4_stream 
  import amba_axi4_stream_pkg::*;
   #(parameter BUS_TYPE  = AXI4_STREAM_BUS_TYPE,
     parameter RTL_FLOW  = AXI4_STREAM_GEN_WITNESS,
     parameter ARM_RCMD  = AXI4_STREAM_ARM_RECOMMENDED,
     parameter MAXWAITS  = AXI4_STREAM_MAXWAITS,
     parameter OPT_SETUP = AXI4_STREAM_CHECK_SETUP,
     parameter OPT_RESET = AXI4_STREAM_RESET_CHECKS,
     parameter RESET_SIM = AXI4_STREAM_RESET_SIM,
     parameter XPROP_EN  = AXI4_STREAM_CHECK_XPROP)
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Module ports, datatypes from the VIP pkg.            *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   (input wire axi4s_aclk    ACLK,
    input wire axi4s_aresetn ARESETn,
    input wire axi4s_data    TDATA,
    input wire axi4s_strb    TSTRB,
    input wire axi4s_keep    TKEEP,
    input wire axi4s_last    TLAST,
    input wire axi4s_id	     TID,
    input wire axi4s_dest    TDEST,
    input wire axi4s_user    TUSER,
    input wire axi4s_valid   TVALID,
    input wire axi4s_ready   TREADY);
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section II: AXI VIP Configuration Rules.             *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   
   /* The AXI VIP only has two configuration 
    * values: 0 (sink) and 1 (source). */
   property using_bus_type_correctly;
      @(posedge ACLK) disable iff (!ARESETn) 
	!(BUS_TYPE > 1);
   endproperty // using_bus_type_correctly
   
   
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section III: Handshake Rules.                        *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   
   /* ,         ,                                                     * 
    * |\\\\ ////| "Once TVALID is asserted it must remain asserted    * 
    * | \\\V/// |  until the handshake (TVALID) occurs".              * 
    * |  |~~~|  | Ref: 2.2.1. Handshake Protocol, p2-3. 	      * 
    * |  |===|  |						      * 
    * |  |A  |  |						      * 
    * |  | X |  |						      * 
    *  \ |  I| /						      * 
    *   \|===|/							      * 
    *    '---'							      */ 
   property tvalid_tready_handshake;
      @(posedge ACLK) disable iff (!ARESETn)
	TVALID && !TREADY |-> ##1 TVALID;
   endproperty // tvalid_tready_handshake
   
   /* ,         ,                                                     * 
    * |\\\\ ////| "The master [...] asserts the TVALID signal HIGH    * 
    * | \\\V/// |  [...] and remains stable until the slave drives    * 
    * |	 |~~~|	|  the TREADY signal high.                            * 
    * |  |===|  |  Transfer takes place once the slave asserts	      * 
    * |  |A  |  |  TREADY HIGH."         		              *  
    * |  | X |  | Ref: 2.2.1 Handshake Protocol, TVALID before	      * 
    *  \ |  I| /       TREADY handshake, p2-3, Figure 2-1.            * 
    *   \|===|/							      * 
    *    '---'							      */
   property tvalid_before_tready;
      @(posedge ACLK) disable iff (!ARESETn) 
	TVALID && !TREADY;
   endproperty // tvalid_before_tready

   /* ,         ,                                                     * 
    * |\\\\ ////|  "Once the master has asserted TVALID, the data or  * 
    * | \\\V/// |   control information from the master must remain   *
    * |	 |~~~|	|   unchanged until the slave drives the TREADY       * 
    * |	 |===|	|   signal HIGH."                                     *
    * |	 |A  |	|   Ref: 2.2.1 Handshake Protocol, p2-3, Figure 2-1.  *  
    * |	 | X |	|   ** This property applies for: TDATA, TID, TLAST   * 
    *  \ |  I| /    TDEST, TUSER, TSTRB and TKEEP.                    * 
    *   \|===|/							      * 
    *    '---'							      */
   property tvalid_control (valid, ready, control);
      @(posedge ACLK) disable iff (!ARESETn) 
	valid && !ready |-> ##1 $stable(control);
   endproperty // tvalid_control
   
   /* ,         ,                                                     * 
    * |\\\\ ////|  "The slave drives TREADY HIGH before the data and  * 
    * | \\\V/// |   control information is valid.                     *
    * |	 |~~~|	|   Transfer takes place once the master asserts      * 
    * |	 |===|	|   TVALID HIGH."                                     * 
    * |	 |A  |	|  Ref: 2.2.1 Handshake Protocol, TREADY before       *  
    * |	 | X |	|             TVALID handshake, p2-4, Figure 2-2.     * 
    *  \ |  I| /                                                      * 
    *   \|===|/							      * 
    *    '---'							      */
   property tready_before_tvalid;
      @(posedge ACLK) disable iff (!ARESETn) 
	TREADY && !TVALID;
   endproperty // tready_before_tvalid
   
   /* ,         ,                                                     * 
    * |\\\\ ////|  "The master asserts TVALID HIGH and the slave      * 
    * | \\\V/// |   asserts TREADY HIGH in the same cycle of ACLK."   *
    * |	 |~~~|	|   Ref: 2.2.1 Handshake Protocol, TVALID with        * 
    * |	 |===|	|              TREADY handshake, p2-4, Figure 2-3.    *
    * |	 |A  |	|                                                     *  
    * |	 | X |	|                                                     * 
    *  \ |  I| /                                                      * 
    *   \|===|/							      * 
    *    '---'							      */
   property tvalid_with_tready;
      @(posedge ACLK) disable iff (!ARESETn)
	TREADY && TVALID;
   endproperty // tvalid_with_tready
   
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section IV: ARM Recommended Rules.                   *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   
   /* ,         ,                                                     * 
    * |\\\\ ////|  "Recommended maximum is 8-bits (TID)".             * 
    * | \\\V/// |   Ref: 2.1 Signal List, p2-2, Table 2-1.            *
    * |	 |~~~|	|                                                     * 
    * |	 |===|	|                                                     *
    * |	 |A  |	|                                                     *  
    * |	 | X |	|                                                     * 
    *  \ |  I| /                                                      * 
    *   \|===|/							      * 
    *    '---'							      */
   property max_size_of_tid;
      @(posedge ACLK) disable iff (!ARESETn)
	!($bits(TID) > 8);
   endproperty // max_size_of_tid
   
   /* ,         ,                                                     * 
    * |\\\\ ////|  "Recommended maximum is 4-bits (TDEST)".           * 
    * | \\\V/// |   Ref: 2.1 Signal List, p2-2, Table 2-1.            *
    * |	 |~~~|	|                                                     * 
    * |	 |===|	|                                                     *
    * |	 |A  |	|                                                     *  
    * |	 | X |	|                                                     * 
    *  \ |  I| /                                                      * 
    *   \|===|/							      * 
    *    '---'							      */
   property max_size_of_tdest;
      @(posedge ACLK) disable iff (!ARESETn)
	!($bits(TDEST) > 4);
   endproperty // max_size_of_tdest

   /* ,         ,                                                     * 
    * |\\\\ ////|  It is recommended that TREADY is asserted within   * 	      
    * | \\\V/// |  MAXWAITS cycles of TVALID being asserted.	      * 
    * |	 |~~~|	|  This is a *potential deadlock check* that can be   *
    * |	 |===|	|  implemented as well using the strong eventually    *
    * |	 |A  |	|  operator (if the required bound is too large to be *
    * |	 | X |	|  formal efficient). Otherwise this bounded property *
    *  \ |  I| /   works fine.                                        * 
    *	\|===|/							      * 
    *	 '---'							      */ 
   property tready_max_wait;
      @(posedge ACLK) disable iff (!ARESETn)
	TVALID & !TREADY |-> ##[1:MAXWAITS] TREADY;
   endproperty // tready_max_wait

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section V: X-Prop Rules.                             *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   
   /* The following X-prop properties are derived from the rules
    * of 2.2.1 Handshake process (TVALID data/control rules).
    * NOTE: Tabby CAD does not support X-prop at the moment.
    *       These rules will be disabled until the X-prop app 
    *       is implemented. */
   
   /* ,         ,                                                     * 
    * |\\\\ ////|  "Once the master has asserted TVALID, the data or  * 
    * | \\\V/// |   control information from the master must remain   *
    * |	 |~~~|	|   unchanged until the slave drives the TREADY       * 
    * |	 |===|	|   signal HIGH (including X-prop)."                  *
    * |	 |A  |	|   Ref: 2.2.1 Handshake Protocol, p2-3, Figure 2-1.  *  
    * |	 | X |	|   ** This property applies for: TDATA, TID, TLAST   * 
    *  \ |  I| /    TDEST, TUSER, TSTRB and TKEEP.                    * 
    *   \|===|/							      * 
    *    '---'							      */
   property xprop_check (antecedent, data_or_control);
      @(posedge ACLK) disable iff (!ARESETn)
	antecedent |-> !$isunknown (data_or_control);
   endproperty // xprop_check

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section VI: Data Signaling Rules.                    *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   
   /* ,         ,                                                     * 
    * |\\\\ ////|  "During reset TVALID must be driven LOW".	      *
    * | \\\V/// |   Ref: 2.7.2 Reset, p2-11.                          * 
    * |	 |~~~|	|						      * 
    * |	 |===|	|						      * 
    * |	 |A  |	|						      * 
    * |	 | X |	|						      * 
    *  \ |  I| /						      * 
    *	\|===|/							      * 
    *	 '---'		                                              */
   property tvalid_during_reset;
      @(posedge ACLK)
	!ARESETn |-> !TVALID;
   endproperty // tvalid_during_reset
   
   /* ,         ,                                                     *
    * |\\\\ ////|  "A master must only begin driving TVALID           *            
    * | \\\V/// |   at a rising ACLK edge following a rising edge at  * 
    * |	 |~~~|	|   at wich ARESETn is asserted HIGH".                *             
    * |	 |===|	|   Ref: 2.7.2 Reset, p2-11, Figure 2-4.	      * 
    * |	 |A  |	|						      * 
    * |	 | X |	|						      * 
    *  \ |  I| /						      * 
    *	\|===|/							      * 
    *	 '---'							      */ 
   logic first_point = 1;
   property exit_from_reset;
      @(posedge ACLK) 
	first_point |-> !TVALID;
   endproperty // exit_from_reset
   
   /* ,         ,                                                     *
    * |\\\\ ////| "TKEEP TSTRB DATA TYPE                              *
    * | \\\V/// |   1     1    Data byte                              *
    * |	 |~~~|	|   1     0    Position byte                          *
    * |	 |===|	|   0     0    Null byte                              *
    * |	 |A  |	|   0     1    Reserved".                             *
    * |	 | X |	|   if TKEEP is high, any TSTRB value is valid.       *
    *  \ |  I| /    if TKEEP is low, only TSTRB LOW is valid.         *
    *	\|===|/	    Ref: 2.4.3 TKEEP and TSTRB combinations, p2-9,    *
    *	 '---'	    Table 2-2.	 				      */
   property tkeep_tstrb_reserved;
      @(posedge ACLK) disable iff (!ARESETn)
	// An invalid scenario that is reserved
	!  
        // occurs when there's any bit in the vector
	(|   
	// whose TKEEP value is LOW and TSTRB is HIGH
	(~TKEEP & TSTRB));   
   endproperty // tkeep_tstrb_reserved
   
   /* ,         ,                                                     *
    * |\\\\ ////| "Data Byte: The associated byte contains valid      * 	      
    * | \\\V/// |  information that must be transmitted between	      * 
    * |	 |~~~|	|  source and destination".			      * 
    * |	 |===|	|  Ref: 2.4.3 TKEEP and TSTRB combinations, p2-9,     * 
    * |	 |A  |	|  Table 2-2.					      * 
    * |	 | X |	|						      * 
    *  \ |  I| /						      * 
    *	\|===|/							      * 
    *	 '---'	   						      */ 
   property data_byte;
      @(posedge ACLK) disable iff (!ARESETn)
	TVALID && (|(TKEEP & TSTRB));
   endproperty // data_byte
   
   /* ,         ,                                                     *
    * |\\\\ ////| "Position Byte: The associated byte indicates the   * 	      
    * | \\\V/// |  relative position of the data bytes in a stream,   * 
    * |	 |~~~|	|  but does not contain any relevant data values".    * 
    * |	 |===|	|  Ref: 2.4.3 TKEEP and TSTRB combinations, p2-9,     * 
    * |	 |A  |	|  Table 2-2.					      * 
    * |	 | X |	|						      * 
    *  \ |  I| /						      * 
    *	\|===|/							      * 
    *	 '---'	   						      */
   property position_byte;
      @(posedge ACLK) disable iff (!ARESETn)
	TVALID && (|(TKEEP & ~TSTRB));
   endproperty // position_byte
   
   /* ,         ,                                                     *
    * |\\\\ ////| "Null Byte: The associated byte does not contain    * 	      
    * | \\\V/// |  information and can be removed from the stream".   *
    * |	 |~~~|	|  Ref: 2.4.3 TKEEP and TSTRB combinations, p2-9,     * 
    * |	 |===|	|  Table 2-2.                                         * 
    * |	 |A  |	|	 					      * 
    * |	 | X |	|						      * 
    *  \ |  I| /						      * 
    *	\|===|/							      * 
    *	 '---'	   						      */ 
   property null_byte;
      @(posedge ACLK) disable iff (!ARESETn)
	TVALID && (|(~TKEEP & ~TSTRB));
   endproperty // null_byte
   
   /* ,         ,                                                     *
    * |\\\\ ////| "If TDATA is not present, it is required that	      * 
    * | \\\V/// |  (TDATA, TSTRB, TKEEP) are not present".	      * 
    * |	 |~~~|	|  Ref: 3.1.5 Optional TDATA, p3-3.		      * 
    * |	 |===|	|  ** This property applies for: TDATA, TSTRB an      * 
    * |	 |A  |	|     TKEEP.					      * 
    * |	 | X |	|						      * 
    *  \ |  I| /						      * 
    *	\|===|/							      * 
    *	 '---'	   						      */ 
   property optional_tdata_behavior (control);
     @(posedge ACLK) disable iff (!ARESETn)
       AXI4_STREAM_DATA_WIDTH_BYTES != 0  | $stable (control);
   endproperty // optional_tdata_behavior
   
   /* ,         ,                                                     *
    * |\\\\ ////| "When asserted, TLAST can be used                   *
    * | \\\V/// |  by a destination to indicate a packet boundary".   *
    * |	 |~~~|	|  Ref: 2.5 Packet boundaries, p2-9.                  * 
    * |	 |===|	| 						      * 
    * |	 |A  |	| 						      * 
    * |	 | X |	|						      * 
    *  \ |  I| /						      * 
    *	\|===|/							      * 
    *	 '---'	   						      */ 
   property packet_boundary;
      @(posedge ACLK) disable iff (!ARESETn)
	TLAST && TVALID && TREADY;
   endproperty // packet_boundary

   /* ,         ,                                                     *
    * |\\\\ ////| "TID, TDEST, and TUSER are all optional signals     *
    * | \\\V/// |  on the interface [...] a master is not required    * 
    * |	 |~~~|	|  to support these output signals".                  * 
    * |	 |===|	|  Ref: 3.1.4 Optional TID, TDEST, and TUSER, p3-3.   * 
    * |	 |A  |	| 						      * 
    * |	 | X |	|						      * 
    *  \ |  I| /						      * 
    *	\|===|/							      * 
    *	 '---'	  						      */ 
   property optional_tid_behavior;
      @(posedge ACLK) disable iff (!ARESETn)
	AXI4_STREAM_ID_WIDTH != 0 | $stable (TID);
   endproperty // optional_tid_behavior

   /* ,         ,                                                     *
    * |\\\\ ////| "TID, TDEST, and TUSER are all optional signals     *
    * | \\\V/// |  on the interface [...] a master is not required    * 
    * |	 |~~~|	|  to support these output signals".                  * 
    * |	 |===|	|  Ref: 3.1.4 Optional TID, TDEST, and TUSER, p3-3.   * 
    * |	 |A  |	| 						      * 
    * |	 | X |	|						      * 
    *  \ |  I| /						      * 
    *	\|===|/							      * 
    *	 '---'	  						      */ 
   property optional_tdest_behavior;
      @(posedge ACLK) disable iff (!ARESETn)
	AXI4_STREAM_DEST_WIDTH != 0 | $stable (TDEST);
   endproperty // optional_tdest_behavior

   /* ,         ,                                                     *
    * |\\\\ ////| "TID, TDEST, and TUSER are all optional signals     *
    * | \\\V/// |  on the interface [...] a master is not required    * 
    * |	 |~~~|	|  to support these output signals".                  * 
    * |	 |===|	|  Ref: 3.1.4 Optional TID, TDEST, and TUSER, p3-3.   * 
    * |	 |A  |	| 						      * 
    * |	 | X |	|						      * 
    *  \ |  I| /						      * 
    *	\|===|/							      * 
    *	 '---'	  						      */ 
   property optional_tuser_behavior;
      @(posedge ACLK) disable iff (!ARESETn)
	AXI4_STREAM_USER_WIDTH != 0 | $stable (TUSER);
   endproperty // optional_tuser_behavior

   
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Section VII: Auxiliary Logic.                        *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   
   always_ff @(posedge ACLK) begin
      if (!ARESETn) first_point <= 1'b1;
      else          first_point <= 1'b0;
   end

   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *		 Rule check definition                                *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */
   generate
      if (OPT_SETUP == 1) begin: setup_checks
	 assert_VIP_correctly_selecting_source_or_sink: assert property (using_bus_type_correctly)
	   else $error ("Cfg Violation: This AXI VIP is not configured as sink (0) or source (1).");
      end
      
      if (ARM_RCMD == 1) begin: arm_recommended_properties
	 assert_VIP_max_size_of_tid: assert property (max_size_of_tid)
	   else $error ("Cfg Violation: The recommended max size of TID is 8-bits (Ref: 2.1 Signal List, p2-2, Table 2-1).");
	 
	 assert_VIP_max_size_of_tdest: assert property (max_size_of_tdest)
	   else $error ("Cfg Violation: The recommended max size of TDEST is 4-bits (Ref: 2.1 Signal List, p2-2, Table 2-1).");
	 
	 if (BUS_TYPE == 1) begin: recommended_tready_maxwait_src
	    assume_SRC_TREADY_MAXWAIT: assume property (tready_max_wait)
	      else $error ("Protocol Violation: TREADY should be asserted within MAXWAITS cycles of TVALID being asserted.");
	 end
	 else begin: recommended_tready_maxwait_snk
	    assert_SNK_TREADY_MAXWAIT: assert property (tready_max_wait)
	      else $error ("Protocol Violation: TREADY should be asserted within MAXWAITS cycles of TVALID being asserted.");
	 end
      end // block: arm_recommended_properties

      if (BUS_TYPE == 1) begin: source_checks
	 assert_SRC_TVALID_until_TREADY: assert property (tvalid_tready_handshake)
	   else $error ("Protocol Violation: Once TVALID is asserted it must remain asserted until the handshake occurs (2.2.1, p2-3).");
	 
	 assert_SRC_STABLE_TDATA: assert property (tvalid_control(TVALID, TREADY, TDATA))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TDATA] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assert_SRC_STABLE_TLAST: assert property (tvalid_control(TVALID, TREADY, TLAST))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TLAST] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assert_SRC_STABLE_TUSER: assert property (tvalid_control(TVALID, TREADY, TUSER))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TUSER] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assert_SRC_STABLE_TSTRB: assert property (tvalid_control(TVALID, TREADY, TSTRB))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TSTRB] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assert_SRC_STABLE_TID:   assert property (tvalid_control(TVALID, TREADY, TID))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TID] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assert_SRC_STABLE_TDEST: assert property (tvalid_control(TVALID, TREADY, TDEST))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TDEST] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assert_SRC_STABLE_TKEEP: assert property (tvalid_control(TVALID, TREADY, TKEEP))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TKEEP] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 if (OPT_RESET == 1) begin: arst_checks
	    if (RESET_SIM == 1) begin: arst_4sim
	       assert_SRC_TVALID_RST:   assert property (tvalid_during_reset)
		 else $error ("Protocol Violation: During reset TVALID must be driven LOW (2.7.2 Reset, p2-11).");
	    end
	    
	    assert_SRC_EXIT_RESET:   assert property (exit_from_reset)
	      else $error ("Protocol Violation: TVALID must be low for the first clock edge that ARESETn goes high (2.7.2 Reset, p2-11, Figure 2-4).");
	 end
	 
	 assert_SRC_TKEEP_TSTRB_RESERVED: assert property (tkeep_tstrb_reserved)
	   else $error ("Protocol Violation: A combination of TKEEP LOW and TSTRB HIGH must not be used (2.4.3 TKEEP and TSTRB combinations, p2-9, Table 2-2).");
	 
	 assert_SRC_OPTIONAL_TDATA_TIEOFF: assert property (optional_tdata_behavior(TDATA))
	   else $error ("Protocol Violation: If TDATA is not present (DATA_WIDTH_MAX = 0), TDATA must be stable (3.1.5 Optional TDATA, p3-3).");
	 
	 assert_SRC_OPTIONAL_TDATA_TSTRB_TIEOFF: assert property (optional_tdata_behavior(TSTRB))
	   else $error ("Protocol Violation: If TDATA is not present (DATA_WIDTH_MAX = 0), TSTRB must be stable (3.1.5 Optional TDATA, p3-3).");
	 
	 assert_SRC_OPTIONAL_TDATA_TKEEP_TIEOFF: assert property (optional_tdata_behavior(TKEEP))
	   else $error ("Protocol Violation: If TDATA is not present (DATA_WIDTH_MAX = 0), TKEEP must be stable (3.1.5 Optional TDATA, p3-3).");
	 
	 assert_SRC_OPTIONAL_TID_TIEOFF: assert property (optional_tid_behavior)
	   else $error ("Protocol Violation: If TID is not present (ID_WIDTH = 0), TID must be stable (3.1.4 Optional TID, TDEST, and TUSER, p3-3).");
	 
	 assert_SRC_OPTIONAL_TDEST_TIEOFF: assert property (optional_tdest_behavior)
	   else $error ("Protocol Violation: If TDEST is not present (DEST_WIDTH = 0), TDEST must be stable (3.1.4 Optional TID, TDEST, and TUSER, p3-3).");
	 
	 assert_SRC_OPTIONAL_TUSER_TIEOFF: assert property (optional_tuser_behavior)
	   else $error ("Protocol Violation: If TUSER is not present (USER_WIDTH = 0), TUSER must be stable (3.1.4 Optional TID, TDEST, and TUSER, p3-3).");
      end // block: source_checks
      else begin : sink_checks
	 assume_SNK_TVALID_until_TREADY: assume property (tvalid_tready_handshake)
	   else $error ("Protocol Violation: Once TVALID is asserted it must remain asserted until the handshake occurs (2.2.1, p2-3).");
	 
	 assume_SNK_STABLE_TDATA: assume property (tvalid_control(TVALID, TREADY, TDATA))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TDATA] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assume_SNK_STABLE_TLAST: assume property (tvalid_control(TVALID, TREADY, TLAST))
           else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TLAST] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assume_SNK_STABLE_TUSER: assume property (tvalid_control(TVALID, TREADY, TUSER))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TUSER] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assume_SNK_STABLE_TSTRB: assume property (tvalid_control(TVALID, TREADY, TSTRB))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TSTRB] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assume_SNK_STABLE_TID:   assume property (tvalid_control(TVALID, TREADY, TID))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TID] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assume_SNK_STABLE_TDEST: assume property (tvalid_control(TVALID, TREADY, TDEST))
	   else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TDEST] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");
	 
	 assume_SNK_STABLE_TKEEP: assume property (tvalid_control(TVALID, TREADY, TKEEP))
           else $error ("Protocol Violation: Once the master has asserted TVALID, data and control information from master must remain stable [TKEEP] until TREADY is asserted (2.2.1, p2-3, Figure 2-1).");

	 if (OPT_RESET == 1) begin: arst_checks
	    if (RESET_SIM == 1) begin: arst_4sim
	       assume_SNK_TVALID_RST:   assume property (tvalid_during_reset)
		 else $error ("Protocol Violation: During reset TVALID must be driven LOW (2.7.2 Reset, p2-11).");
	    end
	    
	    assume_SNK_EXIT_RESET:   assume property (exit_from_reset)
              else $error ("Protocol Violation: TVALID must be low for the first clock edge that ARESETn goes high (2.7.2 Reset, p2-11, Figure 2-4).");
	 end
	 
	 assume_SNK_TKEEP_TSTRB_RESERVED: assume property (tkeep_tstrb_reserved)
           else $error ("Protocol Violation: A combination of TKEEP LOW and TSTRB HIGH must not be used 92.4.3 TKEEP and TSTRB combinations, p2-9, Table 2-2).");
	 
	 assume_SNK_OPTIONAL_TDATA_TIEOFF: assume property (optional_tdata_behavior(TDATA))
           else $error ("Protocol Violation: If TDATA is not present (DATA_WIDTH_MAX = 0), TDATA must be stable (3.1.5 Optional TDATA, p3-3).");
	 
	 assume_SNK_OPTIONAL_TDATA_TSTRB_TIEOFF: assume property (optional_tdata_behavior(TSTRB))
           else $error ("Protocol Violation: If TDATA is not present (DATA_WIDTH_MAX = 0), TSTRB must be stable (3.1.5 Optional TDATA, p3-3).");
	 
	 assume_SNK_OPTIONAL_TDATA_TKEEP_TIEOFF: assume property (optional_tdata_behavior(TKEEP))
	   else $error ("Protocol Violation: If TDATA is not present (DATA_WIDTH_MAX = 0), TKEEP must be stable (3.1.5 Optional TDATA, p3-3).");
	 
	 assume_SRC_OPTIONAL_TID_TIEOFF: assume property (optional_tid_behavior)
	   else $error ("Protocol Violation: If TID is not present (ID_WIDTH = 0), TID must be stable (3.1.4 Optional TID, TDEST, and TUSER, p3-3).");
	 
	 assume_SRC_OPTIONAL_TDEST_TIEOFF: assume property (optional_tdest_behavior)
	   else $error ("Protocol Violation: If TDEST is not present (DEST_WIDTH = 0), TDEST must be stable (3.1.4 Optional TID, TDEST, and TUSER, p3-3).");
	 
	 assume_SRC_OPTIONAL_TUSER_TIEOFF: assume property (optional_tuser_behavior)
	   else $error ("Protocol Violation: If TUSER is not present (USER_WIDTH = 0), TUSER must be stable (3.1.4 Optional TID, TDEST, and TUSER, p3-3).");
      end // block: sink_checks
   endgenerate

   // X-prop checks
   generate
      if (ENABLED_XPROP == 1) begin: xprop_app
	 if (XPROP_EN == 1) begin: xprop_checks
	    if (BUS_TYPE == 1) begin: x_source_checks
	       xprop_SRC_STABLE_TDATA: assert property (xprop_check(TVALID, TDATA)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TDATA is prohibited (2.2.1, p2-3, Figure 2-1).");
	       
	       xprop_SRC_STABLE_TLAST: assert property (xprop_check(TVALID, TLAST)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TLAST is prohibited (2.2.1, p2-3, Figure 2-1).");

	       xprop_SRC_STABLE_TUSER: assert property (xprop_check(TVALID, TUSER))
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TUSER is prohibited (2.2.1, p2-3, Figure 2-1).");

	       xprop_SRC_STABLE_TSTRB: assert property (xprop_check(TVALID, TSTRB)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TSTRB is prohibited (2.2.1, p2-3, Figure 2-1).");

	       xprop_SRC_STABLE_TID: assert property (xprop_check(TVALID, TID)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TID is prohibited (2.2.1, p2-3, Figure 2-1).");

	       xprop_SRC_STABLE_TDEST: assert property (xprop_check(TVALID, TDEST)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TDEST is prohibited (2.2.1, p2-3, Figure 2-1).");

	       xprop_SRC_STABLE_TKEEP: assert property (xprop_check(TVALID, TKEEP)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TKEEP is prohibited (2.2.1, p2-3, Figure 2-1).");

	       xprop_SRC_STABLE_TVALID: assert property (xprop_check(1'b1, TVALID)) 
		 else $error("Protocol Violation: When not in reset state, a don't care value on TVALID is prohibited (2.2.1, p2-3, Figure 2-1).");

	       xprop_SRC_STABLE_READY: assert property (xprop_check(1'b1, TREADY)) 
		 else $error("Protocol Violation: When not in reset state, a don't care value on TREADY is prohibited (2.2.1, p2-3, Figure 2-1).");
	    end // block: x_source_checks
	    else begin: x_sink_checks
	       xprop_SNK_STABLE_TDATA: assume property (xprop_check(TVALID, TDATA)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TDATA is prohibited (2.2.1, p2-3, Figure 2-1).");
	       
	       xprop_SNK_STABLE_TLAST: assume property (xprop_check(TVALID, TLAST)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TLAST is prohibited (2.2.1, p2-3, Figure 2-1).");
	       
	       xprop_SNK_STABLE_TUSER: assume property (xprop_check(TVALID, TUSER))
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TUSER is prohibited (2.2.1, p2-3, Figure 2-1).");
	       
	       xprop_SNK_STABLE_TSTRB: assume property (xprop_check(TVALID, TSTRB)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TSTRB is prohibited (2.2.1, p2-3, Figure 2-1).");
	       
	       xprop_SNK_STABLE_TID: assume property (xprop_check(TVALID, TID)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TID is prohibited (2.2.1, p2-3, Figure 2-1).");
	       
	       xprop_SNK_STABLE_TDEST: assume property (xprop_check(TVALID, TDEST)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TDEST is prohibited (2.2.1, p2-3, Figure 2-1).");
	       
	       xprop_SNK_STABLE_TKEEP: assume property (xprop_check(TVALID, TKEEP)) 
		 else $error("Protocol Violation: When TVALID is asserted, a don't care value on TKEEP is prohibited (2.2.1, p2-3, Figure 2-1).");
	       
	       xprop_SNK_STABLE_TVALID: assume property (xprop_check(1'b1, TVALID)) 
		 else $error("Protocol Violation: When not in reset state, a don't care value on TVALID is prohibited (2.2.1, p2-3, Figure 2-1).");
	       
	       xprop_SNK_STABLE_READY: assume property (xprop_check(1'b1, TREADY)) 
		 else $error("Protocol Violation: When not in reset state, a don't care value on TREADY is prohibited (2.2.1, p2-3, Figure 2-1).");
	    end // block: x_sink_checks
	 end // block: xprop_checks
      end // block: xprop_app
   endgenerate
   
   /* These cover scenarios descriptions are defined in their property block.
    * Remember that, if a cover point is not reached, it is important
    * to check if there is any problem with the logic of the DUT or the
    * AXI Stream VIP configuration. */ 
   cover_TVALID_BEFORE_TREADY: cover property (tvalid_before_tready);
   cover_TREADY_BEFORE_TVALID: cover property (tready_before_tvalid);
   cover_TVALID_WITH_TREADY: cover property (tvalid_with_tready);
   cover_DATA_BYTE: cover property (data_byte);
   cover_POSITION_BYTE: cover property (position_byte);
   cover_NULL_BYTE: cover property (null_byte);
   cover_PACKET_BOUNDARY: cover property (packet_boundary);
endmodule // amba_axi4_stream

