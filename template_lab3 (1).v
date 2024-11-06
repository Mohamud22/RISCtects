// Template for Northwestern - CompEng 361 - Lab3 -- Version 1.1
// Groupname: RISChitects
// NetIDs: yah9076 ; ....

/* to design a single cycle RISC-V CPU which implements the majority of the RV32IM Base Instruction Set. You will eventually use this in the
final lab to implement a pipelined processor. Follow the RISC-V documentation links on Canvas
to learn the instruction encodings and functionality. The specific instructions that you must support are:

lui, auipc
jal, jalr,
beq, bne, blt, bge, bltu, bgeu
lb, lh, lw, lbu, lhu
sb, sh, sw
addi, slti, sltiu
xori, ori, andi
slli, srli, srai,
sll, slt, sltu, srl, sra
add, sub, or, and, xor

as well as multiply/divide instructions:

mul, mulh, mulhsu, mulhu, div, divu, rem, remu

The single cycle processor will be implemented in Verilog (structural w/ continuous assigns – no
behavioral statements) and must have the following interface and port list:
module SingleCycleCPU(halt, clk, rst);
output halt;
input clk, rst;

The halt line should be asserted if and only if the cpu encounters an illegal/unsupported
instruction or there is a memory alignment error (e.g. effective address for a lh is not an
address which is a multiple of two, attempt to fetch from an address which is not a multiple of
four). At that point, your cpu should not execute any more instructions or update any more
system state. The testbench that we have supplied (more on this later) will at that point exit the
simulation and dump system state into files. We will evaluate the correctness of your design
by evaluating the contents of these files.
Your single cycle CPU design should instantiate two library modules. We provide the
implementation for these modules. You should NOT modify them. They are:



*/

//////// RISC_V reference for instructions ///////////////


// branch if equal ; beq rs1, rs2, imm
// branch if not equal ; bne rs1, rs2, imm
// branch if less than ; blt rs1, rs2, imm
// branch if greater than or equal to ; bge rs1, rs2, imm
// branch if less than (unsigned compare) ; bltu rs1, rs2, imm
// branch if greater than or equal to (unsigned compare) ; bgeu rs1, rs2, imm
// load byte ; lb rd, rs1, imm
// load halfword ; lh rd, rs1, imm
// load word ; lw rd, rs1, imm
// load byte unsigned ; lbu rd, rs1, imm
// load halfword usnigned ; lhu rd, rs1, imm
// store byte ; sb rs1, rs2, imm
// store halfword ; sh rs1, rs2, imm
// store word ; sw rs1, rs2, imm



// Some useful defines...please add your own
`define WORD_WIDTH 32
`define NUM_REGS 32

// 7 bit opcode value
`define OPCODE_COMPUTE    7'b0110011      // for R type operations (sll, slt, sltu, srl, sra, add, sub, or, and, xor, mul, mulh, mulhsu, mulhu, div, divu, rem, remu)
`define OPCODE_BRANCH     7'b1100011      // for B type Branch insns (beq, bne, blt, bge, bltu, bgeu)
`define OPCODE_LOAD       7'b0000011      // for I type loads (lb, lh, lw, lbu, lhu)
`define OPCODE_STORE      7'b0100011      // for S type stores (sb, sh, sw)

`define OPCODE_LOADI      7'b0110111      // load immediate ; lui rd, imm
`define OPCODE_AUIPC      7'b0010111      // add upper imm to PC;  auipc rd, imm
`define OPCODE_JAL        7'b1101111      // jump and link; jal rd, imm
`define OPCODE_JALR       7'b1100111      // jump and link register ; rd, rs1, imm
`define OPCODE_COMPUTE_IMM   7'b0010011   // for immediate computes (addi, slti, sltiu, xori, ori, andi, slli, srli, srai)

// 3 bit func3 value for computes
`define FUNC_ADD_SUB      3'b000  // add, sub
`define FUNC_SLL          3'b001  // sll
`define FUNC_SLT          3'b010  // slt
`define FUNC_SLTU         3'b011  // sltu
`define FUNC_XOR          3'b100  // xor
`define FUNC_SRL_SRA      3'b101  // srl, sra
`define FUNC_OR           3'b110  // or
`define FUNC_AND          3'b111  // and
`define FUNC_MUL          3'b000  // mul
`define FUNC_MULH         3'b001  // mulh
`define FUNC_MULHSU       3'b010  // mulhsu
`define FUNC_MULHU        3'b011  // mulhu
`define FUNC_DIV          3'b100  // div
`define FUNC_DIVU         3'b101  // divu
`define FUNC_REM          3'b110  // rem
`define FUNC_REMU         3'b111  // remu

// func3 values for branch instructions (OPCODE_BRANCH)
`define FUNC_BEQ      3'b000  // beq
`define FUNC_BNE      3'b001  // bne
`define FUNC_BLT      3'b100  // blt
`define FUNC_BGE      3'b101  // bge
`define FUNC_BLTU     3'b110  // bltu
`define FUNC_BGEU     3'b111  // bgeu

// func3 values for load instructions (OPCODE_LOAD)
`define FUNC_LB       3'b000  // lb
`define FUNC_LH       3'b001  // lh
`define FUNC_LW       3'b010  // lw
`define FUNC_LBU      3'b100  // lbu
`define FUNC_LHU      3'b101  // lhu

// func3 values for store instructions (OPCODE_STORE)
`define FUNC_SB       3'b000  // sb
`define FUNC_SH       3'b001  // sh
`define FUNC_SW       3'b010  // sw

// func3 for immediates
`define FUNC_ADDI   3'b000   // addi
`define FUNC_SLTI   3'b010   // slti
`define FUNC_SLTIU  3'b011   // sltiu
`define FUNC_XORI   3'b100   // xori
`define FUNC_ORI    3'b110   // ori
`define FUNC_ANDI   3'b111   // andi
`define FUNC_SLLI   3'b001   // slli
`define FUNC_SRLI_SRAI 3'b101 // srli, srai

`define FUNC_JALR 3'b000;  //JALR


// what more auxilary functions do we need??
`define AUX_FUNC_ADD  7'b0000000    // add; also applies for sll, slt, sltu, xor, srl
`define AUX_FUNC_SUB  7'b0100000    // sub
`define AUX_FUNC_M    7'b0000001    // mul...remu
`define AUX_FUNC_SRA_I     7'b0100000    // sra, srai
`define AUX_FUNC_SLLI      7'b0000000     // slli


`define SIZE_BYTE  2'b00
`define SIZE_HWORD 2'b01
`define SIZE_WORD  2'b10


// comment (yafet): I copied these two lines from lab manual (do they need to be here or no since they are already implemented later)
// module Mem(InstAddr, InstOut, DataAddr, DataSize, DataIn, DataOut, WEN, CLK);
// module RegFile(AddrA, DataOutA, AddrB, DataOutB, AddrW, DataInW, WenW, CLK);

module SingleCycleCPU(halt, clk, rst);
   output halt;
   input clk, rst;
   
   wire [`WORD_WIDTH-1:0] PC, InstWord;
   wire [`WORD_WIDTH-1:0] DataAddr, StoreData, DataWord;
   wire [1:0]  MemSize;
   wire        MemWrEn;
   
   wire [4:0]  Rsrc1, Rsrc2, Rdst;
   wire [`WORD_WIDTH-1:0] Rdata1, Rdata2, RWrdata;
   wire        RWrEn;

   wire [`WORD_WIDTH-1:0] NPC, PC_Plus_4;
   wire [6:0]  opcode;

   wire [6:0]  funct7;
   wire [2:0]  funct3;

   wire invalid_op;



   ///// invalid (halt) cases///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   
   // validity check for R-TYPE computes ( add, sll, slt, sltu, srl, sra, sub, or, and, xor, mul, mulh, mulhsu, mulhu, div, divu, rem, remu)

   wire invalid_computes = !((opcode == `OPCODE_COMPUTE) && (
                           // for ADD and SUB
                           ((funct3 == `FUNC_ADD_SUB) &&  ((funct7 == `AUX_FUNC_ADD) || (funct7 == `AUX_FUNC_SUB))) ||
                           // for multiplications
                           ((funct3 == `FUNC_MUL) && (funct7 == `AUX_FUNC_M)) ||
                           ((funct3 == `FUNC_MULH) && (funct7 == `AUX_FUNC_M)) ||
                           ((funct3 == `FUNC_MULHSU) && (funct7 == `AUX_FUNC_M)) ||
                           ((funct3 == `FUNC_MULHU) && (funct7 == `AUX_FUNC_M)) ||
                           // for sll
                           ((funct3 == `FUNC_SLL) && (funct7 == `AUX_FUNC_ADD)) ||
                           // for slt and sltu; they both have the same auxfunc as ADD (0x0)
                           ((funct3 == `FUNC_SLT) && (funct7 == `AUX_FUNC_ADD)) ||
                           ((funct3 == `FUNC_SLTU) && (funct7 == `AUX_FUNC_ADD)) ||
                           // for OR
                           ((funct3 == `FUNC_OR) && (funct7 == `AUX_FUNC_ADD)) ||
                           // for srl and sra; srl has auxfunc of 0x0 and sra has auxfunc of 0x20
                           ((funct3 == `FUNC_SRL_SRA) && 
                             ((funct7 == `AUX_FUNC_SRA_I) || (funct7 == `AUX_FUNC_ADD))) ||
                           // for AND; has auxfunc same as ADD (0x0)
                           ((funct3 == `FUNC_AND) && (funct7 == `AUX_FUNC_ADD)) ||
                           // for XOR; has auxfunc same as ADD (0x0)
                           ((funct3 == `FUNC_XOR) && (funct7 == `AUX_FUNC_ADD)) ||
                           // for division and remainder
                           ((funct3 == `FUNC_DIV) && (funct7 == `AUX_FUNC_M)) ||
                           ((funct3 == `FUNC_DIVU) && (funct7 == `AUX_FUNC_M)) ||
                           ((funct3 == `FUNC_REM) && (funct7 == `AUX_FUNC_M)) ||
                           ((funct3 == `FUNC_REMU) && (funct7 == `AUX_FUNC_M))
                          ));
            
   // validity check for branches, beq, bne, blt, bge, bltu, bgeu
   wire invalid_branch = !((opcode == `OPCODE_BRANCH) && ((funct3 == `FUNC_BEQ) || (funct3 == `FUNC_BGE) || (funct3 == `FUNC_BLT) || (funct3 == `FUNC_BNE) 
                        || (funct3 == `FUNC_BLTU) || (funct3 == `FUNC_BGEU)));

   // validity check for compute immediates (addi, slti, sltiu, xori, ori, andi, slli, srli, srai)
   wire invalid_CommI = !((opcode == `OPCODE_COMPUTE_IMM) && (
                     (funct3 == `FUNC_ADDI) || (funct3 == `FUNC_SLTI) || (funct3 == `FUNC_SLTIU) || (funct3 == `FUNC_XORI) || (funct3 == `FUNC_ORI) || (funct3 == `FUNC_ANDI) || 
                     ((funct3 == `FUNC_SLLI) && (funct7 == `AUX_FUNC_SLLI)) || ((funct3 == `FUNC_SRLI_SRAI) && ((funct7 == `FUNC7_SRLI) || (funct7 == `FUNC7_SRAI))) ));

   // validity check for loads lb, lh, lw, lbu, lhu
   wire invalid_load = !((opcode == `OPCODE_LOAD) && 
                        ((funct3 == `FUNC_LB) || (funct3 == `FUNC_LH) || (funct3 == `FUNC_LW) || (funct3 == `FUNC_LBU) || (funct3 == `FUNC_LHU)));
   
   // validity checker for store (sb, sh, sw)
   wire invalid_store = !(opcode == `OPCODE_STORE) && 
                     ((funct3 == `FUNC_SB) ||
                     (funct3 == `FUNC_SH) ||
                     (funct3 == `FUNC_SW)
                   );

   // validity check for lui
   wire invalid_lui = !(opcode == `OPCODE_LOADI);

   // validity check for auipc
   wire invalid_auipc = !(opcode == `OPCODE_AUIPC);

   // validity check for jal
   wire invalid_jal = !(opcode == `OPCODE_JAL);

   // validity check for jalr
   wire invalid_jalr = !(opcode == `OPCODE_JALR);

   // memory alignment checker
  wire bad_mem_alignment = (
    ((opcode == `OPCODE_LOAD) && ((funct3 == `FUNC_LH) || (funct3 == `FUNC_LHU)) && (DataAddr % 2 != 0)) ||
    ((opcode == `OPCODE_LOAD) && (funct3 == `FUNC_LW) && (DataAddr % 4 != 0)) ||
    ((opcode == `OPCODE_STORE) && (funct3 == `FUNC_SH) && (DataAddr % 2 != 0)) ||
    ((opcode == `OPCODE_STORE) && (funct3 == `FUNC_SW) && (DataAddr % 4 != 0)));

   // now we take the value of each validity check and determine if we have any faults
   wire invalid_case = invalid_computes || invalid_CommI || invalid_branch || invalid_load ||
                         invalid_store || invalid_lui || invalid_auipc || invalid_jal || invalid_jalr;

   assign invalid_op = invalid_case || bad_mem_alignment;

   assign halt = invalid_op; 


 ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////   
   // System State 
   Mem   MEM(.InstAddr(PC), .InstOut(InstWord), 
            .DataAddr(DataAddr), .DataSize(MemSize), .DataIn(StoreData), .DataOut(DataWord), .WE(MemWrEn), .CLK(clk));

   RegFile RF(.AddrA(Rsrc1), .DataOutA(Rdata1), 
	      .AddrB(Rsrc2), .DataOutB(Rdata2), 
	      .AddrW(Rdst), .DataInW(RWrdata), .WenW(RWrEn), .CLK(clk));

   Reg PC_REG(.Din(NPC), .Qout(PC), .WE(1'b1), .CLK(clk), .RST(rst));

   // Instruction Decode
   assign opcode = InstWord[6:0];   
   assign Rdst = InstWord[11:7];       //rd
   assign Rsrc1 = InstWord[19:15];     // rs1
   assign Rsrc2 = InstWord[24:20];     //rs2
   assign funct3 = InstWord[14:12];  // func3 for R-Type, I-Type, S-Type
   assign funct7 = InstWord[31:25];  // auxfunc7 for R-Type

   assign MemWrEn = (opcode == `OPCODE_STORE); // Change this to allow stores, it allows stores
   assign RWrEn = ((opcode == OPCODE_COMPUTE) || (opcode == OPCODE_COMPUTE_IMM) || (opcode == OPCODE_LOAD) || (opcode == OPCODE_JAL) || 
                  (opcode == OPCODE_JALR) || (opcode == OPCODE_LOADI) || (opcode == OPCODE_AUIPC));  // At the moment every instruction will write to the register file

   // to determite size of mem access, we use the lower 2 bits of func3 of lds and stores
   // so 00 is 1 byte access; 01 is 2 bytes (halfword) access; and 10 is 4 bytes (word) access
   assign MemSize = (func3[1:0] ==  SIZE_BYTE) ? `SIZE_BYTE : (func3[1:0] == `SIZE_HWORD) ? `SIZE_HWORD : `SIZE_WORD;

   // Hardwired to support R-Type instructions -- please add muxes and other control signals
   ExecutionUnit EU(.out(RWrdata), .opA(Rdata1), .opB(Rdata2), .func(funct3), .auxFunc(funct7));

   // Fetch Address Datapath
   assign PC_Plus_4 = PC + 4;
   assign NPC = PC_Plus_4;
   
endmodule // SingleCycleCPU


// Incomplete version of Lab2 execution unit
// You will need to extend it. Feel free to modify the interface also
module ExecutionUnit(out, opA, opB, func, auxFunc);
   output [`WORD_WIDTH-1:0] out;
   input [`WORD_WIDTH-1:0]  opA, opB;
   input [2:0] 	 func;
   input [6:0] 	 auxFunc;

   wire [`WORD_WIDTH-1:0] 	 addSub;
   wire [`WORD_WIDTH-1:0] 	 or;


   // Only supports add and subtract
   /* 
   if (opcode == OPCODE_COMPUTE)
   {
      if (func == FUNC_AND)
      {
         compute_out = opA & opB;
      }
      else if (func == FUNC_OR)
      {
         compute_out = opA | opB;
      }
      else if (func == FUNC_ADD_SUB)
      {
         if (auxfunc == AUX_FUNC_ADD)
         {
            compute_out = opA + opB;
         }
         else if (auxfunc == AUX_FUNC_SUB)
         {
            compute_out = opA - opB;
         }
      }
   }

   else if (opcode == OPCODE_BRANCH)
   {
         ....check func3 using if statements 
   }
   ......keep adding more opcode check if statements

   */

   assign addSub = (auxFunc == 7'b0100000) ? (opA - opB) : (opA + opB);
   assign compute_out = ((opcode = OPCODE_COMPUTE) && (func = FUNC_OR) ? (opA | opB) : (func = FUNC_AND) ? (opA & opB) :

   assign out = (func == 3'b000) ? addSub : 32'hXXXXXXXX;
   
endmodule // ExecutionUnit
