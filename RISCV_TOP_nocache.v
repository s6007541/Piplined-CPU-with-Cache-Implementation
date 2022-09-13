module RISCV_TOP (
   //General Signals
   input wire CLK,
   input wire RSTn,
 
   //I-Memory Signals
   output wire I_MEM_CSN,
   input wire [31:0] I_MEM_DI,//input from IM
   output reg [11:0] I_MEM_ADDR,//in byte address
 
   //D-Memory Signals
   output wire D_MEM_CSN,
   input wire [127:0] D_MEM_DI,
   output wire [127:0] D_MEM_DOUT,
   output wire [9:0] D_MEM_ADDR,//in word address
   output wire D_MEM_WEN,
   //output wire [3:0] D_MEM_BE,
 
   //RegFile Signals
   output wire RF_WE,
   output wire [4:0] RF_RA1,
   output wire [4:0] RF_RA2,
   output wire [4:0] RF_WA1,
   input wire [31:0] RF_RD1,
   input wire [31:0] RF_RD2,
   output wire [31:0] RF_WD,
   output wire HALT,                   // if set, terminate program
   output reg [31:0] NUM_INST,         // number of instruction completed
   output wire [31:0] OUTPUT_PORT     // equal RF_WD this port is used for test
   );

reg [3:0] count;
// 4KB memory => need only 12 bit to represent address
reg [11:0] pc;
initial begin
  NUM_INST <= 0;
  count <= 0;
end
 
// TODO: implement pipelined CPU
 
// pipeline reg @@@
reg[3:0] CtlFw1, CtlFw2, CtlFw3, CtlFw4, CtlFw5, nextCtlFw1, nextCtlFw2, nextCtlFw3, nextCtlFw4, nextCtlFw5;
reg [31:0] a1, a2, a3, a4, a5;
reg [31:0] a1_next, a2_next, a3_next, a4_next, a5_next;
reg [31:0] b1, b2, b3, b4, b5;
reg [31:0] b1_next, b2_next, b3_next, b4_next, b5_next;
reg [31:0] ALUout1, ALUout2, ALUout3, ALUout4, ALUout5;
reg [31:0] ALUout1_next, ALUout2_next, ALUout3_next, ALUout4_next, ALUout5_next;
reg [31:0] mdr;
reg [31:0] mdr_next;
reg [31:0] ir;
reg [31:0] ir_next;
reg [31:0] ir1,ir2,ir3;
reg [31:0] ir1_next,ir2_next,ir3_next;
reg [31:0] Imm1, Imm2, Imm3, Imm4, Imm5;
reg [31:0] Imm1_next, Imm2_next, Imm3_next, Imm4_next, Imm5_next;
reg [4:0] rs11, rs12, rs13, rs14, rs15;
reg [4:0] rs11_next, rs12_next, rs13_next, rs14_next, rs15_next;
reg [4:0] rs21, rs22, rs23, rs24, rs25;
reg [4:0] rs21_next, rs22_next, rs23_next, rs24_next, rs25_next;
reg [4:0] rd1, rd2, rd3, rd4, rd5;
reg [4:0] rd1_next, rd2_next, rd3_next, rd4_next, rd5_next;
// control signal @@@
 
// reg PCWrite;  write back to pc
reg PCWrite1, PCWrite2, PCWrite3, PCWrite4, PCWrite5;
// reg IorD;  decide input to memory to be PC or ALUout
reg IorD1, IorD2, IorD3, IorD4, IorD5;
// reg MemRead; // put memory content from memory to memory data output : IF
reg MemRead1, MemRead2, MemRead3, MemRead4, MemRead5;
// reg MemWrite;  allow write data to memory
reg MemWrite1, MemWrite2, MemWrite3, MemWrite4, MemWrite5;
// reg IRWrite; // write output from memory to instruction register IR : IF
reg IRWrite1, IRWrite2, IRWrite3, IRWrite4, IRWrite5;
// reg RegDst; // write address of register (rt or rd)
reg RegDst1, RegDst2, RegDst3, RegDst4, RegDst5;
// reg MemtoReg; // data going to store in reg is from ALUout or MDR
reg MemtoReg1, MemtoReg2, MemtoReg3, MemtoReg4, MemtoReg5;
// reg RegWrite; // write MDR to RF
reg RegWrite1, RegWrite2, RegWrite3, RegWrite4, RegWrite5;
// reg ALUSrcA;
reg ALUSrcA1, ALUSrcA2, ALUSrcA3, ALUSrcA4, ALUSrcA5;
// reg [1:0] ALUSrcB;
reg [1:0] ALUSrcB1, ALUSrcB2, ALUSrcB3, ALUSrcB4, ALUSrcB5;
// reg [1:0] ALUOp; // 00 = add, 01 = subtract, 10 = funct from instruction : EX
reg [1:0] ALUOp1, ALUOp2, ALUOp3, ALUOp4, ALUOp5;
// reg [1:0] PCSrc; // next pc is pc+4 or branch target or jump target
reg  [1:0] PCSrc1, PCSrc2, PCSrc3, PCSrc4, PCSrc5;
// reg PCWriteCond; // allow pc to update if branch condition is true (result = 0)
reg PCWriteConde1, PCWriteConde2, PCWriteConde3, PCWriteConde4, PCWriteConde5;
 
 
// decode the instruction 32 bit length
wire [6:0] OP_CODE =   ir[6:0];
wire [4:0] RD =   ir[11:7];
wire [4:0] RS1 =   ir[19:15];
wire [4:0] RS2 =   ir[24:20];
wire [2:0] func3 =   ir[14:12];
wire [6:0] func7 =   ir[31:25];
 
// b. JAL // 1101111
// c. JALR // 1100111
// d. BEQ, BNE, BLT, BGE, BLTU, BGEU //1100011
// e. LW // 0000011
// f. SW // 0100011
// g. ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI // 0010011
// h. ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND // 0110011
// @@@
reg LUI_r, AUIPC_r, JAL_r, JALR_r, BRANCH_r, LOAD_r, STORE_r, ARI_r,AR_r ;
wire JAL =  OP_CODE == 7'b1101111; // U type - J immediate
wire JALR =  OP_CODE == 7'b1100111; // I type - I immediate
wire BRANCH = OP_CODE == 7'b1100011; // S type - B immediate
wire LOAD = OP_CODE == 7'b0000011; // I type - I immediate
wire STORE = OP_CODE == 7'b0100011;  // S type - S immediate
wire ARI = OP_CODE == 7'b0010011;  // I type - I immediate
wire AR = OP_CODE == 7'b0110011; // R type
reg JAL1,JAL2,JAL3;
reg JAL1_next,JAL2_next,JAL3_next;
reg JALR1,JALR2,JALR3;
reg JALR1_next,JALR2_next,JALR3_next;
reg BRANCH1,BRANCH2,BRANCH3;
reg BRANCH1_next,BRANCH2_next,BRANCH3_next;
reg LOAD1,LOAD2,LOAD3;
reg LOAD1_next,LOAD2_next,LOAD3_next;
reg STORE1,STORE2,STORE3;
reg STORE1_next,STORE2_next,STORE3_next;
reg ARI1,ARI2,ARI3;
reg ARI1_next,ARI2_next,ARI3_next;
reg AR1,AR2,AR3;
reg AR1_next,AR2_next,AR3_next;
reg [11:0] pc1,pc2,pc3,pc4;
reg [11:0] pc1_next,pc2_next,pc3_next,pc4_next;
reg [2:0] func31,func32,func33;
reg [2:0] func31_next,func32_next,func33_next;
reg [6:0] func71,func72,func73;
reg [6:0] func71_next,func72_next,func73_next;
reg [31:0] result1, result2, result3;
reg [31:0] result1_next, result2_next, result3_next;
reg disable1, disable2, disable3;
reg disable1_next, disable2_next, disable3_next;
// immediate registers @@@
wire [31:0] I_imm = {ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],
                  ir[30:25], ir[24:21],ir[20]};
wire [31:0] S_imm = {ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],
                  ir[30:25], ir[11:8],ir[7]};
wire [31:0] B_imm = {ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],
                  ir[7], ir[30:25], ir[11:8], 1'b0};
wire [31:0] U_imm = {ir[31], ir[30:20], ir[19:12],12'b000000000000};
wire [31:0] J_imm = {ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],ir[31],
                  ir[19:12], ir[20],ir[30:25],ir[24:21],1'b0};
wire [31:0] imm =   (JAL) ? J_imm :
                  (JALR || LOAD || ARI) ? I_imm:
                  (STORE) ? S_imm :
                  (BRANCH) ? B_imm : 0;
                
 
reg finish, finish_next;
reg temp = 0;
reg available1, available2, available3, available4, available5;
reg available2_next, available3_next, available4_next, available5_next;
// forwarding unit
reg LOAD_HAZARD1, LOAD_HAZARD2, flag1, flag2;
 
 
// Only allow for NUM_INST
always @ (negedge CLK) begin
  if (RSTn && !disable3 && available5) begin
      NUM_INST <= NUM_INST + 1;
      // $display("%d", NUM_INST);
  end
 end
always @(*) begin // IF
  if(!(LOAD_HAZARD1 || LOAD_HAZARD2)) begin
      available2_next = available1;
      I_MEM_ADDR = pc;
      ir_next = I_MEM_DI;
      pc1_next = pc;
  end
end
 
 
// ALU for AR, ARI, BRANCH condition, LOAD, STORE
wire [31:0] result = (AR1 && (func31 == 3'b000) && func71 == 7'b0000000) ? a1 + b1 : // ADD
                  (AR1 && (func31 == 3'b000) && func71 == 7'b0100000) ? a1 - b1 : // SUB
                  (AR1 && (func31 == 3'b001)) ? a1 << b1[4:0] : // SLL
                  (AR1 && (func31 == 3'b010)) ? $signed(a1) < $signed(b1) : //SLT sign less than
                  (AR1 && (func31 == 3'b011)) ? a1 < b1 : //SLTU unsign less than
                  (AR1 && (func31 == 3'b100)) ? a1 ^ b1 : //XOR
                  (AR1 && (func31 == 3'b101) && func71 == 7'b0000000) ? a1 >> b1[4:0] : //SRL
                  (AR1 && (func31 == 3'b101) && func71 == 7'b0100000) ? (a1 >>> b1[4:0]) : //SRA
                  (AR1 && (func31 == 3'b110)) ? a1 | b1 :
                  (AR1 && (func31 == 3'b111)) ? a1 & b1 :
                  BRANCH1 && (func31 == 3'b000) ? (a1 == b1) :
                  BRANCH1 && (func31 == 3'b010) ? (a1 != b1) :
                  BRANCH1 && (func31 == 3'b100) ? ($signed(a1) < $signed(b1)) :
                  BRANCH1 && (func31 == 3'b101) ? ($signed(a1) >= $signed(b1)) :
                  BRANCH1 && (func31 == 3'b110) ? (a1 < b1) :
                  BRANCH1 && (func31 == 3'b111) ? (a1 >= b1) :
                  ARI1 && (func31 == 3'b000) ? (a1 + Imm1) : // ADDI
                  ARI1 && (func31 == 3'b001) ? (a1 << Imm1[4:0]) : //SLLI
                  ARI1 && (func31 == 3'b010) ? ($signed(a1) < $signed(Imm1)) : //SLTI
                  ARI1 && (func31 == 3'b011) ? (a1 < Imm1) : //SLTIU
                  ARI1 && (func31 == 3'b100) ? (a1 ^ Imm1) : //XORI
                  ARI1 && (func31 == 3'b101) && func71 == 7'b0000000 ? (a1 >> Imm1[4:0]) : //SRLI
                  ARI1 && (func31 == 3'b101) && func71 == 7'b0100000 ? (a1 >>> Imm1[4:0]) : //SRAI
                  ARI1 && (func31 == 3'b110) ? (a1 | Imm1) : // ORI
                  ARI1 && (func31 == 3'b111) ? (a1 & Imm1) : // ANDI
                  LOAD1 || STORE1 ? a1 + Imm1 :
                  JAL || JALR ? pc1 + 4 : 0;
// ALU for jump and branch
wire [31:0] branch_des = pc1 + imm;
wire [11:0] pc_jump = JAL ? (pc1 + imm) :
                      JALR ? (RF_RD1 + imm) & 32'hfffffffe :
                      BRANCH ? branch_des[11:0] : 0;
 
always @(*) begin // ID
    
  if(JAL1 || JALR1 || (BRANCH1 && (result == 1)) || (BRANCH2 && (result1 == 0)) || LOAD_HAZARD1 || LOAD_HAZARD2) begin
      disable1_next = 1;
      ir1_next = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
      available3_next = 1'bx;
      pc2_next = 12'bxxxxxxxxxxxx;
      rs11_next = 5'bxxxxx;
      rs21_next = 5'bxxxxx;
      rd1_next = 5'bxxxxx;
      Imm1_next = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
      a1_next = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
      b1_next = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
      func31_next = 3'bxxx;
      func71_next = 7'bxxxxxxx;
      JAL1_next = 1'bx;
      JALR1_next = 1'bx;
      BRANCH1_next = 1'bx;
      LOAD1_next = 1'b0;
      STORE1_next = 1'bx;
      ARI1_next = 1'bx;
      AR1_next = 1'bx;
  end
  else begin
      ir1_next = ir;
      available3_next = available2;
      pc2_next = pc1;
      rs11_next = RS1;
      rs21_next = RS2;
      rd1_next = RD;
      Imm1_next = imm;
    
      a1_next = RF_RD1;
      b1_next = RF_RD2;
      func31_next = func3;
      func71_next = func7;
      JAL1_next = JAL;
      JALR1_next = JALR;
      BRANCH1_next = BRANCH;
      LOAD1_next = LOAD;
      STORE1_next = STORE;
      ARI1_next = ARI;
      AR1_next = AR;
      disable1_next = 0;
  end
end
 
 
 
always @(*) begin // EX
  ir2_next = ir1;
  available4_next = available3;
  disable2_next = disable1;
  pc3_next = pc2;
  ALUout1_next = result;
   a2_next = a1;
  b2_next = b1;
  rs12_next = rs11;
  rs22_next = rs21;
  rd2_next = rd1;
  result1_next = result;
  JAL2_next = JAL1;
  JALR2_next = JALR1;
  BRANCH2_next = BRANCH1;
  LOAD2_next = LOAD1;
  STORE2_next = STORE1;
  ARI2_next = ARI1;
  AR2_next = AR1;
  func32_next = func31;
  func72_next = func71;
 
 
 
end
always @(*) begin // MEM
  ir3_next = ir2;
  available5_next = available4;
   pc4_next = pc3;
  a3_next = a2;
  b3_next = b2;
  rs13_next = rs12;
  rs23_next = rs22;
  rd3_next = rd2;
 
  mdr_next = D_MEM_DI[31:0];
 
 
 
   result2_next = result1;
   JAL3_next = JAL2;
  JALR3_next = JALR2;
  BRANCH3_next = BRANCH2;
  LOAD3_next = LOAD2;
  STORE3_next = STORE2;
  ARI3_next = ARI2;
  AR3_next = AR2;
  func33_next = func32;
  func73_next = func72;
  disable3_next = disable2;
 end
// forwarding unit
 
// forwarding unit
// reg LOAD_HAZARD1, LOAD_HAZARD2, flag1, flag2;
 
always @(*) begin
  if(RSTn) begin
      available1 = 1;
      disable1 = 0;
      pc = 0;
      LOAD_HAZARD1 = 0;
      LOAD_HAZARD2 = 0;
  end
end
always @(*) begin
  if(flag1 && LOAD3 && !LOAD_HAZARD1) begin
      a1 = mdr;
      flag1 = 0;
  end
  if(flag2 && LOAD3 && !LOAD_HAZARD2) begin
      b1 = mdr;
      flag2 = 0;
  end
 end
always @(*) begin
  if(LOAD1 && (rd1 == RS1 || rd1 == RS2)) begin
      if(rd1 == RS1) begin
          LOAD_HAZARD1 = 1;
          flag1 = 1;
      end
      if(rd1 == RS2) begin
          LOAD_HAZARD2 = 1;
          flag2 = 1;
      end
  end
  else begin
      LOAD_HAZARD1 = 0;
      LOAD_HAZARD2 = 0;
      // case load hazard to next 2 instruction
      if(LOAD3 && (rd3 == rs11 || rd3 == rs21) && !disable1_next) begin
          if(rd3 == rs11)  begin
              a1 = mdr;
          end
          if(rd3 == rs21)  begin
              b1 = mdr;
          end
      end
  end
 end
always @(*) begin
  if((JAL2) | (JALR2)| (AR2) | (ARI2) && rd2 == rs11) begin
      a1 = result1;
      // $display("--------------------------------------------------A1");
  end
  else if((JAL3) | (JALR3) | (AR3) | (ARI3) && rd3 == rs11) begin
      a1 = result2;
      // $display("--------------------------------------------------A2");
  end
  if((JAL2) | (JALR2)  | (AR2) | (ARI2) && rd2 == rs21) begin
      b1 = result1;
      // $display("--------------------------------------------------B1");
  end
  else if((JAL3) | (JALR3) | (AR3) | (ARI3) && rd3 == rs21) begin
      b1 = result2;
      // $display("--------------------------------------------------B2");
  end
end
 
// reg [3:0] count;
 
always @(posedge CLK) begin
  if(RSTn) begin
      //if no load hazard
   if((LOAD2 || STORE2) && count <= 6) begin
       available5 <= 0;
       disable3 <= 1;
       count <= count + 1;
   end
   else begin
       count <= 0;
       if(!(LOAD_HAZARD1 || LOAD_HAZARD2)) begin
           if(!disable1_next ) begin
               if(JAL || JALR) begin
                   pc <= pc_jump;
               end
               else if(BRANCH) begin
                   // always taken branch
                   pc <= pc_jump;
               end
               else if (BRANCH1 && result == 0) begin
                   pc <= pc1 + 4;
               end
               else begin //BRANCH2 && result == 1 && other cases
                   pc <= pc + 4;
               end
              
              
           end
           else begin
               pc <= pc+4;
           end
           // allow IF -> ID update
           available2 <= available2_next;
           ir <= ir_next;
           pc1 <= pc1_next;
       end 
  
       mdr <= mdr_next;
  
       rs11 <= rs11_next;
       rs12 <= rs12_next;
       rs13 <= rs13_next;
  
       rs21 <= rs21_next;
       rs22 <= rs22_next;
       rs23 <= rs23_next;
  
       rd1 <= rd1_next;
       rd2 <= rd2_next;
       rd3 <= rd3_next;
  
      
       ir1 <= ir1_next;
       ir2 <= ir2_next;
       ir3 <= ir3_next;
  
      
       available3 <= available3_next;
       available4 <= available4_next;
       available5 <= available5_next;
  
      
       pc2 <= pc2_next;
       pc3 <= pc3_next;
       pc4 <= pc4_next;
  
  
       disable1 <= disable1_next;
       disable2 <= disable2_next;
       disable3 <= disable3_next;
  
       a1 <= a1_next;
       a2 <= a2_next;
       a3 <= a3_next;
       b1 <= b1_next;
       b2 <= b2_next;
       b3 <= b3_next;
  
       Imm1 <= Imm1_next;
  
       ALUout1 <= ALUout1_next;
       ALUout2 <= ALUout2_next;
  
  
       JAL1 <= JAL1_next;
       JALR1 <= JALR1_next;
       BRANCH1 <= BRANCH1_next;
       LOAD1 <= LOAD1_next;
       STORE1 <= STORE1_next;
       ARI1 <= ARI1_next;
       AR1 <= AR1_next;
  
       JAL2 <= JAL2_next;
       JALR2 <= JALR2_next;
       BRANCH2 <= BRANCH2_next;
       LOAD2 <= LOAD2_next;
       STORE2 <= STORE2_next;
       ARI2 <= ARI2_next;
       AR2 <= AR2_next;
  
       JAL3 <= JAL3_next;
       JALR3 <= JALR3_next;
       BRANCH3 <= BRANCH3_next;
       LOAD3 <= LOAD3_next;
       STORE3 <= STORE3_next;
       ARI3 <= ARI3_next;
       AR3 <= AR3_next;
  
       func31 <= func31_next;
       func32 <= func32_next;
       func33 <= func33_next;
       func71 <= func71_next;
       func72 <= func72_next;
       func73 <= func73_next;
  
       result1 <= result1_next;
       result2 <= result2_next;
       result3 <= result3_next;
 
   end
 
  end
 
end
// terminate by halt
assign HALT = (a3 == 32'h0000000c && ir3 == 32'h00008067) ? 1 : 0;
// instruction memory
assign I_MEM_CSN =  RSTn ? 0 : 1;
// register file
assign RF_WE = ((JAL3) | (JALR3) | (LOAD3) | (AR3) | (ARI3)); // write enable
assign RF_RA1 = RS1;
assign RF_RA2 = RS2;
assign RF_WA1 = rd3; // for load and AR, ARI
// data memory
assign D_MEM_CSN =  RSTn&&((LOAD2 || STORE2) && count == 0) ? 0 : 1;
assign D_MEM_WEN = STORE2 ? 0 : 1; //write operation enable negative
assign D_MEM_DOUT = b2; // value to store
assign D_MEM_ADDR = result1[9:0]; //effective address for load and store
assign D_MEM_BE = (STORE2 && func32 == 3'b000) ? 4'b0001 : //SB
              (STORE2 && func32 == 3'b001) ? 4'b0011 : //SH
              (STORE2 && func32 == 3'b010) ? 4'b1111 : //SW
              (LOAD2 && func32 == 3'b000) ? 4'b0001 : //LB
              (LOAD2 && func32 == 3'b001) ? 4'b0011 : //LH
              (LOAD2 && func32 == 3'b010) ? 4'b1111 : 4'b1111; //LW
//Write Back Stage
assign RF_WD = (LOAD3) ? mdr : // load
             (AR3 || ARI3) ? result2 : // R-type
             (STORE3) ? result2[11:0]:
             (BRANCH3) ? result2 :
             (JAL3 || JALR3) ? pc4+4 : RF_WD;
assign OUTPUT_PORT = RF_WD;
 
endmodule //