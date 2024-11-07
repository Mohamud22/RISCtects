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


Parts to complete:

  Mohamud:
      - Branch
      - store
      - loadI
      - auipc
      - Jal
      - JalR
  Yafet:
    - all computes
    - all compute immediates
    - load
    
Branch:


wire [31:0] next_Branch;
 // BRANCH  / section 2.7 of the book
 assign bne_result = (Rsrc1!=Rsrc2);
 assign beq_result = (Rsrc1== Rsrc2)
 assign blt_result =($signed(Rsrc1) < $signed(Rsrc2)); // not sure if we could use "signed" 
 assign bge_result = ($signed(Rsrc1) >= $signed(Rsrc2));
 assign bltu_result = (Rsrc1 < Rsrc2);
 assign bgeu_result = (Rsrc1 >= Rsrc2);
 //next_Branch address
 assign next_Branch = PC +(imm << 1); // shift imm by 1 bit to the left 
 
