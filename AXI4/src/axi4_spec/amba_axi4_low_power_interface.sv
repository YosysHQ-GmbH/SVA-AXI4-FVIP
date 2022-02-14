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
`ifndef __AMBA_AXI4_LOW_POWER_INTERFACE__
 `define __AMBA_AXI4_LOW_POWER_INTERFACE__
package amba_axi4_low_power_interface;
   /*		 ><><><><><><><><><><><><><><><><><><><><             *
    *	      Section A9.2.3 Acceptance of low-power request          *
    *		 ><><><><><><><><><><><><><><><><><><><><	      */

   /* ,         ,                                                     *
    * |\\\\ ////|  "In Figure A9-1 (T1), the system clock controller  *
    * | \\\V/// |   drives CSYSREQ LOW to request the peripheral to   *
    * |	 |~~~|	|   enter low-power state". See that CSYSACK is HIGH  *
    * |	 |===|	|   when that event occurs.                           *
    * |	 |A  |	|                                                     *
    * |	 | X |	|   Ref: A9.2.2 Power-down or power-up handshake,     *
    *  \ |  I| /	 pA9-107, Figure A9-1.                        *
    *	\|===|/							      *
    *	 '---'							      */
   property csysreq_fall(csysreq, csysack);
      (@(negedge csysreq) csysack);
   endproperty // csysreq_fall

   /* ,         ,                                                     *
    * |\\\\ ////|  "In Figure A9-1 (T3), the system clock controller  *
    * | \\\V/// |   drives CSYSREQ HIGH, to require exit from         *
    * |	 |~~~|	|   low-power state". See that CSYSACK is low when    *
    * |	 |===|	|   that event occurs.                                *
    * |	 |A  |	|                                                     *
    * |	 | X |	|   Ref: A9.2.2 Power-down or power-up handshake,     *
    *  \ |  I| /	 pA9-107, Figure A9-1.                        *
    *	\|===|/							      *
    *	 '---'							      */
   property csysreq_rise(csysreq, csysack);
      (@(posedge csysreq) ~csysack);
   endproperty // csysreq_rise

   /* ,         ,                                                     *
    * |\\\\ ////|  "In Figure A9-1, the peripheral acknowledges the   *
    * | \\\V/// |   request at time T2 by driving CSYSACK LOW". See   *
    * |	 |~~~|	|   that CSYSREQ is low when that event occurs.       *
    * |	 |===|	|                                                     *
    * |	 |A  |	|   Ref: A9.2.2 Power-down or power-up handshake,     *
    * |	 | X |	|        pA9-107, Figure A9-1.                        *
    *  \ |  I| /	                                              *
    *	\|===|/							      *
    *	 '---'							      */
   property csysack_fall(csysack, csysreq);
      (@(negedge csysack) ~csysreq);
   endproperty // csysack_fall
   

   /* ,         ,                                                     *
    * |\\\\ ////|  "In Figure A9-1, at T4, the peripheral drives      *
    * | \\\V/// |   CSYSACK HIGH to acknowledge the exit". See that   *
    * |	 |~~~|	|   CSYSREQ is HIGH when that event occurs.           *
    * |	 |===|	|                                                     *
    * |	 |A  |	|   Ref: A9.2.2 Power-down or power-up handshake,     *
    * |	 | X |	|        pA9-107, Figure A9-1.                        *
    *  \ |  I| /	                                              *
    *	\|===|/							      *
    *	 '---'							      */
   property csysack_rise(csysack, csysreq);
      (@(posedge csysack) csysreq);
   endproperty // csysack_rise
   
endpackage // amba_axi4_low_power_interface
`endif
