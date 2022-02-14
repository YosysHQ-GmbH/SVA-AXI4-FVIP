`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Original file prepared by Mahdad Davari
//////////////////////////////////////////////////////////////////////////////////


module mat_mul #
	(
        parameter integer DIM_LOG = 2,     /* matrix dimention in log2; e.g. A[8][8] has the DIM of 8, DIM_LOG of 3, and SIZE of 64; change this as desired;
                                              you will need to set this parameter in the testbench file as well. */
        parameter integer DIM = 2**DIM_LOG,
        parameter integer SIZE = DIM*DIM,
        parameter integer SIZE_LOG = 2*DIM_LOG,
        parameter integer DATA_WIDTH = 32
    )
    (
        // Clock and Reset shared with the AXI-Lite Slave Port
		input wire  s00_axi_aclk,
		input wire  s00_axi_aresetn,
		
		// AXI-Stream Slave
		output wire  s00_axis_tready,
		input wire [DATA_WIDTH-1 : 0] s00_axis_tdata,
		input wire  s00_axis_tlast,
        input wire  s00_axis_tvalid,
        
        // AXI-Stream Master
		output wire  m00_axis_tvalid,
        output wire [DATA_WIDTH-1 : 0] m00_axis_tdata,
        output wire [(DATA_WIDTH/8)-1 : 0] m00_axis_tstrb,
        output wire  m00_axis_tlast,
        input wire  m00_axis_tready,
        
        // Matrix-select and Start signals coming from the AXI-Lite Slave Port
        input wire sel,
        input wire start
    );

    // (state) control flags
	reg busy;              // Accelerator is busy computing
	reg item_done;         // one item of the result matrix is ready
	reg matrix_done;       // the whole result matrix is ready
	reg start_transfer;    // start of transferring the result matrix back to the PS
	reg transfer;          // accelerator is transferring the results back
	reg last_transfer;     // last item of the result being transferred
	reg mac_enable;        // mac register will be updated with the value of multiply-and-add
    
    // Block RAMs
    reg [DATA_WIDTH-1 : 0] mem_A [0 : SIZE-1]; // BRAM for matrix A
    reg [DATA_WIDTH-1 : 0] mem_B [0 : SIZE-1]; // BRAM for matrix B
    reg [DATA_WIDTH-1 : 0] mem_R [0 : SIZE-1]; // BRAM for the result matrix
    
    // BRAM Output Registers 
    reg [DATA_WIDTH-1 : 0] mat_A;   // matrix A read-out
    reg [DATA_WIDTH-1 : 0] mat_B;   // matrix B read-out
    reg [DATA_WIDTH-1 : 0] mat_R;   // result matrix read-out

    // Stream-In and Stream-out addresses
    reg [SIZE_LOG-1 : 0] addr_stream_in;    // address used to fill in matrices A and B
    reg [SIZE_LOG-1 : 0] addr_stream_out;   // address used to read-out and transfer the result matrix

    // Addresses used to read from and write to the matrices during the multiplication
    wire [SIZE_LOG-1 : 0] addr_A;   // address used to read from matrix A during multiplication
    wire [SIZE_LOG-1 : 0] addr_B;   // address used to read from matrix B during multiplication
    reg [SIZE_LOG-1 : 0] addr_R;    // address used to write to the result matrix during multiplication; note that this address is register, not wire!
    
    // Counters used to traverse the matrices during the multiplication
    reg [DIM_LOG-1 : 0] row_cnt;    // row counter; indicates the row of the multiplication
    reg [DIM_LOG-1 : 0] col_cnt;    // column counter; indicates the column of the multiplication
    reg [DIM_LOG-1 : 0] tmp_cnt;    // temporary counter; indicates the intermediate index of the multiplication
    
    // multiply-and-addition
    wire [DATA_WIDTH-1 : 0] mad;    // multiply and addition of intermediate values during multiplication
    reg [DATA_WIDTH-1 : 0] mac;     // the previous mad value (i.e. accumulator)
    
    
    // Accelerator is ready to receive data
    assign s00_axis_tready = !busy && !transfer; // TODO: when should the accelerator accept new data? refer to the control flags declared above;
    
    // Stream-in address: generates the next address for the stream-in data
    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn || s00_axis_tlast)
            addr_stream_in <= 0;
        else if (s00_axis_tready && s00_axis_tvalid) // TODO: When should the address change? refer to the AXI-Stream Slave protocol and the control flags.
            addr_stream_in <= addr_stream_in + 1; // TODO: what should the next address be?
    end
    
    // Matrix A BRAM
    always @ (posedge s00_axi_aclk) begin 
        if (s00_axis_tready && s00_axis_tvalid && !sel) // TODO: write-enable signal; when should we write to the matrix A? refer to the AXI-Stream Slave protocol and the control flags.
            mem_A [addr_stream_in] <= s00_axis_tdata;
        if (busy) // TODO: read-enable signal; when should we read from the matrix A? refer to the control flags.
            mat_A <= mem_A [addr_A];
    end
    
    // Matrix B BRAM
    always @ (posedge s00_axi_aclk) begin
        if (s00_axis_tready && s00_axis_tvalid && sel) // TODO: write-enable signal; when should we write to the matrix B? refer to the AXI-Stream Slave protocol and the control flags.
            mem_B [addr_stream_in] <= s00_axis_tdata;
        if (busy) // TODO: read-enable signal; when should we read from the matrix B? refer to the control flags.
            mat_B <= mem_B [addr_B];
    end
    
    // Stream-Out Data via AXI-Stream Master    
    assign m00_axis_tstrb = 4'hf;   // always f; byte-enable signal;
    assign m00_axis_tdata = mat_R;       // TODO: where do the stream-out data (result) come from?
    assign m00_axis_tlast = last_transfer;       // TODO: when should we set the signal for the last stream-out? refer to the control flags;
    assign m00_axis_tvalid = transfer;      // TODO: when are the stream-out data valid? refer to the control flags;
    
    // Stream-Out Address: generates the next stream-out address
    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn || last_transfer) // TODO: when should we reset the stream-out address? refer to the control flags;
            addr_stream_out <= 0;
        else if ((start_transfer || transfer) && m00_axis_tready && !busy) // TODO: When should the address change? refer to the AXI-Stream Master protocol and the control flags.
           addr_stream_out <= addr_stream_out + 1; // TODO: what should the next address be?
    end
    
    // Start the transfer of the results to the PS
    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn)
            start_transfer <= 0;
        else
            start_transfer <= matrix_done; // TODO: refer to the control signals; this signal shall be asserted for one clock cycle.
    end
    
    // Accelerator is busy transferring the results back to the PS
    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn || last_transfer) // TODO: when to reset? refer to the control signals.
            transfer <= 0;
        else if (start_transfer)  // TODO: refer to the control signals; this signal shall remain asserted while transferring the results.
            transfer <= 1;
    end
    
    // Transferring the last result
    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn)
            last_transfer <= 0;
        else
            last_transfer <= addr_stream_out == SIZE - 1; // TODO: this signal should be asserted for one clock cycle when transferring the last address.
    end
    
    // Result matrix BRAM
    always @ (posedge s00_axi_aclk) begin
        if (item_done) // TODO: write-enable signal; when should we write to the result matrix? refer to the control flags.
            mem_R [addr_R] <= mad; // TODO: which value should we write to the result matrix? Where does the multiplication result come from?
        if ((start_transfer || transfer) && m00_axis_tready && !last_transfer) // TODO: read-enable signal; when should we read from the result matrix? refer to the AXI-Stream Master protocol and the control flags.
            mat_R <= mem_R [addr_stream_out];
    end
    
    // Accelerator is busy multiplying
    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn || matrix_done || transfer) // TODO: when is the accelerator not multiplying? refer to the control flags.
            busy <= 0;
        else if (start) // TODO: when is the accelerator busy multiplying? this signal shall be asserted while the accelerator is multiplying.
            busy <= 1'b1;
    end
    
    // One item of the result matrix is ready
    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn)
            item_done <= 0;
        else
            item_done <= tmp_cnt == DIM - 1; // TODO: this signal should be asserted when computing the last partial value in a row and column; refer to the address counters.
    end
    
    // The whole result matrix is ready
    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn)
            matrix_done <= 0;
        else
            matrix_done <=  row_cnt == DIM - 1 && col_cnt == DIM - 1 && tmp_cnt == DIM - 1 ; // TODO: this signal should be asserted when computing the last partial value in the last row and column; refer to the address counters.
    end
    
    // Temporary counter for the inner-most loop when computing the partial (intermediate) values
    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn || tmp_cnt == DIM - 1 || matrix_done) // TODO: when to reset? refer to the control flags.
            tmp_cnt <= 0;
        else if (busy) // TODO: when to increment the inner-most loop? refer to the control flags.
            tmp_cnt <= tmp_cnt + 1;
    end
    
    // Column counter
    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn || matrix_done) // TODO: when to reset? refer to the control flags.
            col_cnt <= 0;
        else if (tmp_cnt == DIM - 1) // TODO: when to increment? refer to the (multiplication) loop order.
            col_cnt <= col_cnt + 1;
    end
    
    // Row counter
    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn || matrix_done) // TODO: when to reset? refer to the control flags.
            row_cnt <= 0;
        else if (col_cnt == DIM - 1 && tmp_cnt == DIM - 1) // TODO: when to increment? refer to the (multiplication) loop order.
            row_cnt <= row_cnt + 1;
    end
    
    // Addresses used during the multiplication
    assign addr_A = (DIM * row_cnt) + tmp_cnt;  // TODO: refer to the matrix dimension and the loop counters
    assign addr_B = (DIM * tmp_cnt) + col_cnt; // TODO: refer to the matrix dimension and the loop counters

    always @ (posedge s00_axi_aclk) begin
        if (!s00_axi_aresetn || start)
            addr_R <= 0;
        else if (busy) // TODO: when to increment the address used to write to the result matrix? refer to the control flags. 
            addr_R <= (DIM * row_cnt) + col_cnt; // TODO: what should the next address be?
    end
        
    // Multiply-and-Add
    assign mad = mat_A * mat_B + mac;

    // [multiply-and-]Accumulator (partial sum)
    always @ (posedge s00_axi_aclk) begin
       if (!s00_axi_aresetn || item_done) // TODO: when to reset the partial sum? refer to the control flags (inner-most loop)
           mac <= 0;
       else if (mac_enable)
           mac <= mad; // TODO: what is the partial sum?
    end
    
    // MAC-Enable
    always @ (posedge s00_axi_aclk) begin
       if (!s00_axi_aresetn)
           mac_enable <= 0;
       else
           mac_enable <= busy; // TODO: when to write to the MAC? refer to the control flags.
    end
        
endmodule