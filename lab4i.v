`define WORD_WIDTH 32
`define NUM_REGS 32
// Opcodes for instructions
`define OPCODE_COMPUTE     7'b0110011
`define OPCODE_BRANCH      7'b1100011
`define OPCODE_LOAD        7'b0000011
`define OPCODE_STORE       7'b0100011
`define OPCODE_LUI         7'b0110111
`define OPCODE_AUIPC       7'b0010111
`define OPCODE_JAL         7'b1101111
`define OPCODE_JALR        7'b1100111
`define OPCODE_COMPUTE_IMM 7'b0010011

// Functional definitions for compute instructions
`define FUNC_ADD_SUB  3'b000
`define FUNC_SLL      3'b001
`define FUNC_SLT      3'b010
`define FUNC_SLTU     3'b011
`define FUNC_XOR      3'b100
`define FUNC_SRL_SRA  3'b101
`define FUNC_OR       3'b110
`define FUNC_AND      3'b111

// Latency definitions for long-latency operations
`define LATENCY_MUL   4
`define LATENCY_DIV  20

module PipelinedCPU(halt, clk, rst);
    output halt;
    input clk, rst;

    // Program Counter and pipeline registers
    reg [`WORD_WIDTH-1:0] PC;
    reg [`WORD_WIDTH-1:0] IF_ID_PC, IF_ID_Inst;
    reg [`WORD_WIDTH-1:0] ID_EX_PC, ID_EX_Rdata1, ID_EX_Rdata2, ID_EX_Immediate;
    reg [4:0] ID_EX_Rdst;
    reg [6:0] ID_EX_opcode;
    reg [2:0] ID_EX_funct3;
    reg [6:0] ID_EX_funct7;

    reg [`WORD_WIDTH-1:0] EX_MEM_ALUOut, EX_MEM_Rdata2;
    reg [4:0] EX_MEM_Rdst;
    reg [6:0] EX_MEM_opcode;
    
    reg [`WORD_WIDTH-1:0] MEM_WB_ALUOut;
    reg [`WORD_WIDTH-1:0] MEM_WB_MemData;
    reg [4:0] MEM_WB_Rdst;
    reg [6:0] MEM_WB_opcode;

    wire [`WORD_WIDTH-1:0] InstWord, DataWord, ALUResult, Immediate;
    wire [4:0] Rsrc1, Rsrc2, Rdst;
    wire [6:0] opcode;
    wire [2:0] funct3;
    wire [6:0] funct7;
    wire MemWrEn, RWrEn, ALUSrc, Jump, Branch;
    wire [`WORD_WIDTH-1:0] NPC, branch_target, jump_target;

    // Forwarding and hazard control
    wire [1:0] forwardA_sel, forwardB_sel;
    wire stall;
    wire [`WORD_WIDTH-1:0] alu_inputA, alu_inputB;

    // Multiply/divide stall control
    reg [5:0] mult_div_counter;
    wire is_mult_div;

    // Instantiate Memory and Register File
    wire [`WORD_WIDTH-1:0] RF_ReadData1, RF_ReadData2, MEM_ReadData;

    /*RegFile RF (
        .clk(clk),
        .rst(rst),
        .readReg1(Rsrc1),
        .readReg2(Rsrc2),
        .writeReg(MEM_WB_Rdst),
        .writeData(MEM_WB_ALUOut),
        .writeEnable(RWrEn),
        .readData1(RF_ReadData1),
        .readData2(RF_ReadData2)
    );
*/
   RegFile RF(.AddrA(Rsrc1), .DataOutA(Rdata1), 
	      .AddrB(Rsrc2), .DataOutB(Rdata2), 
	      .AddrW(Rdst), .DataInW(DRin), .WenW(RWrEn), .CLK(clk));
   
   /*Mem MEM (
        .clk(clk),
        .rst(rst),
        .address(EX_MEM_ALUOut),
        .writeData(EX_MEM_Rdata2),
        .writeEnable(MemWrEn),
        .readData(MEM_ReadData)
    );
*/
   Mem MEM(.InstAddr(PC), .InstOut(InstWord), 
           .DataAddr(DataAddr), .DataSize(), 
           .DataIn(StoreData), .DataOut(DataWord), 
           .WE(MemWrEn), .CLK(clk));
    // Instruction Fetch (IF) stage
    always @(posedge clk or posedge rst) begin
        if (rst)
            PC <= 0;
        else if (!stall)
            PC <= NPC;
    end

    assign NPC = (Branch) ? branch_target : (Jump ? jump_target : PC + 4);

    // Instruction Decode (ID) stage
    assign Rsrc1 = IF_ID_Inst[19:15];
    assign Rsrc2 = IF_ID_Inst[24:20];
    assign Rdst = IF_ID_Inst[11:7];
    assign opcode = IF_ID_Inst[6:0];
    assign funct3 = IF_ID_Inst[14:12];
    assign funct7 = IF_ID_Inst[31:25];

    assign Immediate = (opcode == `OPCODE_COMPUTE_IMM || opcode == `OPCODE_LOAD || opcode == `OPCODE_JALR) ?
                       {{20{IF_ID_Inst[31]}}, IF_ID_Inst[31:20]} :
                       (opcode == `OPCODE_STORE) ?
                       {{20{IF_ID_Inst[31]}}, IF_ID_Inst[31:25], IF_ID_Inst[11:7]} :
                       (opcode == `OPCODE_BRANCH) ?
                       {{20{IF_ID_Inst[31]}}, IF_ID_Inst[7], IF_ID_Inst[30:25], IF_ID_Inst[11:8], 1'b0} :
                       (opcode == `OPCODE_JAL) ?
                       {{12{IF_ID_Inst[31]}}, IF_ID_Inst[19:12], IF_ID_Inst[20], IF_ID_Inst[30:21], 1'b0} :
                       (opcode == `OPCODE_LUI || opcode == `OPCODE_AUIPC) ?
                       {IF_ID_Inst[31:12], 12'b0} : 32'b0;

    // Execution (EX) stage
    assign is_mult_div = (ID_EX_opcode == `OPCODE_COMPUTE) && ((ID_EX_funct7 == `LATENCY_MUL) || (ID_EX_funct7 == `LATENCY_DIV));

    always @(posedge clk or posedge rst) begin
        if (rst)
            mult_div_counter <= 0;
        else if (is_mult_div)
            mult_div_counter <= (mult_div_counter == 0) ?
                                 ((ID_EX_funct7 == `LATENCY_MUL) ? `LATENCY_MUL : `LATENCY_DIV) : mult_div_counter - 1;
        else
            mult_div_counter <= 0;
    end

    assign alu_inputA = (forwardA_sel == 2'b10) ? EX_MEM_ALUOut :
                        (forwardA_sel == 2'b01) ? MEM_WB_ALUOut : ID_EX_Rdata1;

    assign alu_inputB = (forwardB_sel == 2'b10) ? EX_MEM_ALUOut :
                        (forwardB_sel == 2'b01) ? MEM_WB_ALUOut : (ALUSrc ? ID_EX_Immediate : ID_EX_Rdata2);

    // ALU Operations
    ExecutionUnit EU(
        .out(ALUResult),
        .opA(alu_inputA),
        .opB(alu_inputB),
        .func(ID_EX_funct3),
        .auxFunc(ID_EX_funct7),
        .opcode(ID_EX_opcode)
    );

    assign stall = is_mult_div && (mult_div_counter != 0);

    // Memory Access (MEM) stage
    assign MemWrEn = (EX_MEM_opcode == `OPCODE_STORE);

    // Write Back (WB) stage
    assign RWrEn = (MEM_WB_opcode == `OPCODE_COMPUTE) ||
                   (MEM_WB_opcode == `OPCODE_COMPUTE_IMM) ||
                   (MEM_WB_opcode == `OPCODE_LOAD) ||
                   (MEM_WB_opcode == `OPCODE_LUI) ||
                   (MEM_WB_opcode == `OPCODE_AUIPC);

    assign halt = 0; // Halt logic remains incomplete

endmodule

module ExecutionUnit(out, opA, opB, func, auxFunc, opcode);
    output [`WORD_WIDTH-1:0] out;
    input [`WORD_WIDTH-1:0] opA, opB;
    input [2:0] func;
    input [6:0] auxFunc;
    input [6:0] opcode;

    reg [`WORD_WIDTH-1:0] result;

    always @(*) begin
        case (func)
            `FUNC_ADD_SUB: result = (auxFunc[5]) ? (opA - opB) : (opA + opB);
            `FUNC_SLL:     result = opA << opB[4:0];
            `FUNC_SLT:     result = ($signed(opA) < $signed(opB)) ? 32'b1 : 32'b0;
            `FUNC_SLTU:    result = (opA < opB) ? 32'b1 : 32'b0;
            `FUNC_XOR:     result = opA ^ opB;
            `FUNC_SRL_SRA: result = (auxFunc[5]) ? ($signed(opA) >>> opB[4:0]) : (opA >> opB[4:0]);
            `FUNC_OR:      result = opA | opB;
            `FUNC_AND:     result = opA & opB;
            default:       result = 32'b0;
        endcase
    end

    assign out = result;
endmodule
