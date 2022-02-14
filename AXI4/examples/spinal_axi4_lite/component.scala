/*  AXI4 Formal Properties.
 *
 *  Copyright (C) 2020  Diego Hernandez <diego@yosyshq.com>
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
package axi4.lite.formal
import spinal.core._
import spinal.lib._
import spinal.lib.bus.amba4.axilite._

class LogicFunction extends Component {
  val io = new Bundle {
    val port_a = in UInt (16 bits)
    val port_b = in UInt (16 bits)
    val port_r = out UInt (32 bits)
  }
  
  io.port_r := io.port_a * io.port_b
}

class AxiLite4FormalComponent extends Component {
  val io = new Bundle {
    val bus = slave (AxiLite4 (AxiLite4Config (addressWidth = 32,
                                               dataWidth = 32)))
    val o_result = out UInt (32 bits)
  }

  val ctrl = new AxiLite4SlaveFactory (io.bus)
  var AxiFunction = new LogicFunction ()
  ctrl.driveAndRead (AxiFunction.io.port_a, address = 0)
  ctrl.driveAndRead (AxiFunction.io.port_b, address = 4)
  ctrl.read (AxiFunction.io.port_r, address = 8)

  io.o_result := AxiFunction.io.port_r
}

object RtlGen {
  def main (args: Array[String]) {
    SpinalVerilog (new AxiLite4FormalComponent)
  }
}
