// Generator : SpinalHDL v1.3.2    git head : 41815ceafff4e72c2e3a3e1ff7e9ada5202a0d26
// Date      : 09/11/2020, 14:04:40
// Component : AxiLite4FormalComponent

`default_nettype wire
module LogicFunction (
      input  [15:0] io_port_a,
      input  [15:0] io_port_b,
      output [31:0] io_port_r);
  assign io_port_r = (io_port_a * io_port_b);
endmodule

module AxiLite4FormalComponent (
      input   io_bus_aw_valid,
      output  io_bus_aw_ready,
      input  [31:0] io_bus_aw_payload_addr,
      input  [2:0] io_bus_aw_payload_prot,
      input   io_bus_w_valid,
      output  io_bus_w_ready,
      input  [31:0] io_bus_w_payload_data,
      input  [3:0] io_bus_w_payload_strb,
      output  io_bus_b_valid,
      input   io_bus_b_ready,
      output [1:0] io_bus_b_payload_resp,
      input   io_bus_ar_valid,
      output  io_bus_ar_ready,
      input  [31:0] io_bus_ar_payload_addr,
      input  [2:0] io_bus_ar_payload_prot,
      output  io_bus_r_valid,
      input   io_bus_r_ready,
      output [31:0] io_bus_r_payload_data,
      output [1:0] io_bus_r_payload_resp,
      output [31:0] io_o_result,
      input   clk,
      input   reset);
  wire [31:0] AxiFunction_io_port_r;
  wire  ctrl_readHaltRequest;
  wire  ctrl_writeHaltRequest;
  wire  ctrl_writeJoinEvent_valid;
  wire  ctrl_writeJoinEvent_ready;
  wire  _zz_1_;
  wire [1:0] ctrl_writeRsp_resp;
  wire  _zz_2_;
  wire  _zz_3_;
  wire  _zz_4_;
  reg  _zz_5_;
  reg [1:0] _zz_6_;
  wire  ctrl_readDataStage_valid;
  wire  ctrl_readDataStage_ready;
  wire [31:0] ctrl_readDataStage_payload_addr;
  wire [2:0] ctrl_readDataStage_payload_prot;
  reg  _zz_7_;
  reg [31:0] _zz_8_;
  reg [2:0] _zz_9_;
  reg [31:0] ctrl_readRsp_data;
  wire [1:0] ctrl_readRsp_resp;
  wire  _zz_10_;
  wire  _zz_11_;
  wire  ctrl_writeOccur;
  wire  ctrl_readOccur;
  reg [15:0] AxiFunction_io_port_a__driver;
  reg [15:0] AxiFunction_io_port_b__driver;
  LogicFunction AxiFunction ( 
    .io_port_a(AxiFunction_io_port_a__driver),
    .io_port_b(AxiFunction_io_port_b__driver),
    .io_port_r(AxiFunction_io_port_r) 
  );
  assign ctrl_readHaltRequest = 1'b0;
  assign ctrl_writeHaltRequest = 1'b0;
  assign _zz_1_ = (ctrl_writeJoinEvent_valid && ctrl_writeJoinEvent_ready);
  assign ctrl_writeJoinEvent_valid = (io_bus_aw_valid && io_bus_w_valid);
  assign io_bus_aw_ready = _zz_1_;
  assign io_bus_w_ready = _zz_1_;
  assign ctrl_writeJoinEvent_ready = (_zz_3_ && _zz_2_);
  assign _zz_2_ = (! ctrl_writeHaltRequest);
  assign _zz_3_ = ((1'b1 && (! _zz_4_)) || io_bus_b_ready);
  assign _zz_4_ = _zz_5_;
  assign io_bus_b_valid = _zz_4_;
  assign io_bus_b_payload_resp = _zz_6_;
  assign io_bus_ar_ready = ((1'b1 && (! ctrl_readDataStage_valid)) || ctrl_readDataStage_ready);
  assign ctrl_readDataStage_valid = _zz_7_;
  assign ctrl_readDataStage_payload_addr = _zz_8_;
  assign ctrl_readDataStage_payload_prot = _zz_9_;
  assign _zz_10_ = (! ctrl_readHaltRequest);
  assign ctrl_readDataStage_ready = (_zz_11_ && _zz_10_);
  assign io_bus_r_valid = (ctrl_readDataStage_valid && _zz_10_);
  assign _zz_11_ = io_bus_r_ready;
  assign io_bus_r_payload_data = ctrl_readRsp_data;
  assign io_bus_r_payload_resp = ctrl_readRsp_resp;
  assign ctrl_writeRsp_resp = (2'b00);
  assign ctrl_readRsp_resp = (2'b00);
  always @ (*) begin
    ctrl_readRsp_data = (32'b00000000000000000000000000000000);
    case(ctrl_readDataStage_payload_addr)
      32'b00000000000000000000000000000000 : begin
        ctrl_readRsp_data[15 : 0] = AxiFunction_io_port_a__driver;
      end
      32'b00000000000000000000000000000100 : begin
        ctrl_readRsp_data[15 : 0] = AxiFunction_io_port_b__driver;
      end
      32'b00000000000000000000000000001000 : begin
        ctrl_readRsp_data[31 : 0] = AxiFunction_io_port_r;
      end
      default : begin
      end
    endcase
  end

  assign ctrl_writeOccur = (ctrl_writeJoinEvent_valid && ctrl_writeJoinEvent_ready);
  assign ctrl_readOccur = (io_bus_r_valid && io_bus_r_ready);
  assign io_o_result = AxiFunction_io_port_r;
  always @ (posedge clk or negedge reset) begin
    if (!reset) begin
      _zz_5_ <= 1'b0;
      _zz_7_ <= 1'b0;
    end else begin
      if(_zz_3_)begin
        _zz_5_ <= (ctrl_writeJoinEvent_valid && _zz_2_);
      end
      if(io_bus_ar_ready)begin
        _zz_7_ <= io_bus_ar_valid;
      end
    end
  end

  always @ (posedge clk) begin
    if(_zz_3_)begin
      _zz_6_ <= ctrl_writeRsp_resp;
    end
    if(io_bus_ar_ready)begin
      _zz_8_ <= io_bus_ar_payload_addr;
      _zz_9_ <= io_bus_ar_payload_prot;
    end
    case(io_bus_aw_payload_addr)
      32'b00000000000000000000000000000000 : begin
        if(ctrl_writeOccur)begin
          AxiFunction_io_port_a__driver <= io_bus_w_payload_data[15 : 0];
        end
      end
      32'b00000000000000000000000000000100 : begin
        if(ctrl_writeOccur)begin
          AxiFunction_io_port_b__driver <= io_bus_w_payload_data[15 : 0];
        end
      end
      32'b00000000000000000000000000001000 : begin
      end
      default : begin
      end
    endcase
  end
endmodule

