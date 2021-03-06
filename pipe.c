/*
 * ECE 18-447, Spring 2013
 *
 * MIPS pipeline timing simulator
 *
 * Chris Fallin, 2012
 */

#include "pipe.h"
#include "shell.h"
#include "mips.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>

// #define DEBUG

/* debug */
void print_op(Pipe_Op *op)
{
    if (op)
        printf("OP (PC=%08x inst=%08x) src1=R%d (%08x) src2=R%d (%08x) dst=R%d valid %d (%08x) br=%d taken=%d dest=%08x mem=%d addr=%08x\n",
                op->pc, op->instruction, op->reg_src1, op->reg_src1_value, op->reg_src2, op->reg_src2_value, op->reg_dst, op->reg_dst_value_ready,
                op->reg_dst_value, op->is_branch, op->branch_taken, op->branch_dest, op->is_mem, op->mem_addr);
    else
        printf("(null)\n");
}

/* global pipeline state */
Pipe_State pipe;

Cache instr_cache[64][4];
Cache data_cache[256][8];

PHT global_pattern[256];
BTB branch_buffer[1024];

int cycle_count = 0;

uint32_t data_set_number;   //Extract only bits 5 to 12 ( up to 256)

uint32_t data_current_tag;  //Extract bits 13 to 31
uint8_t GHR;

void pipe_init()
{
    memset(&pipe, 0, sizeof(Pipe_State));
    pipe.PC = 0x00400000; 
}

void pipe_cycle(){
    cycle_count++;
#ifdef DEBUG
    printf("\n\n----\n\nPIPELINE:\n");
    printf("DCODE: "); print_op(pipe.decode_op);
    printf("EXEC : "); print_op(pipe.execute_op);
    printf("MEM  : "); print_op(pipe.mem_op);
    printf("WB   : "); print_op(pipe.wb_op);
    printf("\n");
#endif

    if(cycle_count % 100000 == 0){
        printf("===================================\n");
        printf("        Cycle No. %d\n", cycle_count);
        printf("===================================\n");
    }

    pipe_stage_wb();
    //immediately stop once syscall was written back
    if(RUN_BIT == 0) return;
    pipe_stage_mem();
    pipe_stage_execute();
    pipe_stage_decode();
    pipe_stage_fetch();

    /* handle branch recoveries */
    if (pipe.branch_recover) {
#ifdef DEBUG
        printf("branch recovery: new dest %08x flush %d stages\n", pipe.branch_dest, pipe.branch_flush);
#endif
        if (pipe.branch_dest != pipe.PC){
            pipe.instr_stall_count = 0;
            pipe.instr_stall_state = false;
        }

        pipe.PC = pipe.branch_dest;

        if (pipe.branch_flush >= 2) {
            if (pipe.decode_op) free(pipe.decode_op);
            pipe.decode_op = NULL;
        }

        if (pipe.branch_flush >= 3) {
            if (pipe.execute_op) free(pipe.execute_op);
            pipe.execute_op = NULL;
        }

        if (pipe.branch_flush >= 4) {
            if (pipe.mem_op) free(pipe.mem_op);
            pipe.mem_op = NULL;
        }

        if (pipe.branch_flush >= 5) {
            if (pipe.wb_op) free(pipe.wb_op);
            pipe.wb_op = NULL;
        }

        pipe.branch_recover = 0;
        pipe.branch_dest = 0;
        pipe.branch_flush = 0;

        stat_squash++;
    }
}

void pipe_recover(int flush, uint32_t dest)
{
    /* if there is already a recovery scheduled, it must have come from a later
     * stage (which executes older instructions), hence that recovery overrides
     * our recovery. Simply return in this case. */
    if (pipe.branch_recover) return;

    /* schedule the recovery. This will be done once all pipeline stages simulate the current cycle. */
    pipe.branch_recover = 1;
    pipe.branch_flush = flush;
    pipe.branch_dest = dest;
}

void pipe_stage_wb()
{
    /* if there is no instruction in this pipeline stage, we are done */
    if (!pipe.wb_op)
        return;

    /* grab the op out of our input slot */
    Pipe_Op *op = pipe.wb_op;
    pipe.wb_op = NULL;

    /* if this instruction writes a register, do so now */
    if (op->reg_dst != -1 && op->reg_dst != 0) {
        pipe.REGS[op->reg_dst] = op->reg_dst_value;
#ifdef DEBUG
        printf("R%d = %08x\n", op->reg_dst, op->reg_dst_value);
#endif
    }

    /* if this was a syscall, perform action */
    if (op->opcode == OP_SPECIAL && op->subop == SUBOP_SYSCALL) {
        if (op->reg_src1_value == 0xA) {
            pipe.PC = op->pc + 4; /* fetch will do pc += 4, then we stop with correct PC */
            RUN_BIT = 0;
        }
    }

    /* free the op */
    free(op);

    stat_inst_retire++;
}

void update_data_recentness(int i){
    for (int k = 0; k < 8; k++){
        if (data_cache[data_set_number][k].tag != 0){
            data_cache[data_set_number][k].recentness += 1;
        }
    }
    data_cache[data_set_number][i].recentness = 1; //Set that block's recency to 1, and the first slot to 1 (lower = newer)
}

_Bool check_data_cache(Pipe_Op *op) //Returns true for cache miss or false for cache hit
{
    /* Loop through each cache block */
    for (int i = 0; i < 8; i++){
        // printf("Tag in Struct (Data): %d\n", data_cache[data_set_number][i].tag);
        /* see if this cache array postion contains our instruction */
        if (data_cache[data_set_number][i].tag == data_current_tag && data_cache[data_set_number][i].recentness != 0){ // Cache hit
            // printf("Data Cache Hit\n");
            return false; //True if stall, false if no stall
        }
    }
    pipe.data_stall_count = 50;
    return true; //cache miss (stall)
}

void store_data_cache(Pipe_Op *op){ //Takes in the PC value and store it into the appropriate position
    /* Case 1 - Cache Miss - when there is an empty block, store into the first empty slot (numerical order) for that block*/ 
    for (int i = 0; i < 8; i++){
        if (data_cache[data_set_number][i].tag == 0){ //Empty block exists (tag is empty for that block)
            //store the data and tag into that block, and add recency to it
            data_cache[data_set_number][i].tag = data_current_tag;
            update_data_recentness(i);
            return;
        }
    }
    //Case 2 - cache miss without any empty space left -replace the oldest (highest value) with this new PC
    uint32_t oldest_recency = 0;
    int oldest_position;

    //Find the oldest value, and store the corresponding block index
    for(int i = 0; i < 8; i++){
        if (oldest_recency < data_cache[data_set_number][i].recentness){
            oldest_recency = data_cache[data_set_number][i].recentness;
            oldest_position = i;
        }
    }
    data_cache[data_set_number][oldest_position].tag = data_current_tag;
    update_data_recentness(oldest_position);
    return;
}

void pipe_stage_mem()
{
    /* if there is no instruction in this pipeline stage, we are done */
    if (!pipe.mem_op)
        return;

    /* grab the op out of our input slot */
    Pipe_Op *op = pipe.mem_op;

    /* Instert Stalling Check Algo here =================================================*/
    data_set_number = (op->mem_addr >> 5) & 0xFF; //Extract only bits 5 to 12 ( up to 256)
    data_current_tag = (op->mem_addr >> 13); // & 0x1FFFFF; //Extract bits 13 to 31 (19 bits)
    
    /* check instr cache stall */
    if (pipe.data_stall_state == true){
        pipe.data_stall_count -= 1;
    }

    //Only check data cache if this is a load/store op
    if (pipe.data_stall_state == false && op->is_mem == 1){
        // Check the set index to look for the set with the current pipe's PC
        pipe.data_stall_state = check_data_cache(op); // accesses instr cache & store value without implementing delay 
        //returns false if cache hit, and true for cache miss 
    }

    if (pipe.data_stall_count == 1){
        /* This branch would only be entered in the 50th (last stall) cycle */
        /* Store this pipe.pc into the designated cache block*/ // Might need to store PC from the first cycle if that changes
        store_data_cache(op);
    }
    
    if (pipe.data_stall_state == true && pipe.data_stall_count != 0){
        return;
    }

    if (pipe.data_stall_count == 0){
        /* Set stall state to false to check the cache again in the next cycle */
        pipe.data_stall_state = false;
    }
    /* ===================================================================== */

    //Loading the data from main memory using the address obtained from the execution stage (mem_addr)
    uint32_t val = 0;
    if (op->is_mem)
        val = mem_read_32(op->mem_addr & ~3);

    switch (op->opcode) {
        case OP_LW:
        case OP_LH:
        case OP_LHU:
        case OP_LB:
        case OP_LBU:
            {
                /* extract needed value */
                op->reg_dst_value_ready = 1;
                if (op->opcode == OP_LW) {
                    op->reg_dst_value = val;
                }
                else if (op->opcode == OP_LH || op->opcode == OP_LHU) {
                    if (op->mem_addr & 2)
                        val = (val >> 16) & 0xFFFF;
                    else
                        val = val & 0xFFFF;

                    if (op->opcode == OP_LH)
                        val |= (val & 0x8000) ? 0xFFFF8000 : 0;

                    op->reg_dst_value = val;
                }
                else if (op->opcode == OP_LB || op->opcode == OP_LBU) {
                    switch (op->mem_addr & 3) {
                        case 0:
                            val = val & 0xFF;
                            break;
                        case 1:
                            val = (val >> 8) & 0xFF;
                            break;
                        case 2:
                            val = (val >> 16) & 0xFF;
                            break;
                        case 3:
                            val = (val >> 24) & 0xFF;
                            break;
                    }

                    if (op->opcode == OP_LB)
                        val |= (val & 0x80) ? 0xFFFFFF80 : 0;

                    op->reg_dst_value = val;
                }
            }
            break;

        case OP_SB:
            switch (op->mem_addr & 3) {
                case 0: val = (val & 0xFFFFFF00) | ((op->mem_value & 0xFF) << 0); break;
                case 1: val = (val & 0xFFFF00FF) | ((op->mem_value & 0xFF) << 8); break;
                case 2: val = (val & 0xFF00FFFF) | ((op->mem_value & 0xFF) << 16); break;
                case 3: val = (val & 0x00FFFFFF) | ((op->mem_value & 0xFF) << 24); break;
            }

            mem_write_32(op->mem_addr & ~3, val);
            break;

        case OP_SH:
#ifdef DEBUG
            printf("SH: addr %08x val %04x old word %08x\n", op->mem_addr, op->mem_value & 0xFFFF, val);
#endif
            if (op->mem_addr & 2)
                val = (val & 0x0000FFFF) | (op->mem_value) << 16;
            else
                val = (val & 0xFFFF0000) | (op->mem_value & 0xFFFF);
#ifdef DEBUG
            printf("new word %08x\n", val);
#endif

            mem_write_32(op->mem_addr & ~3, val);
            break;

        case OP_SW:
            val = op->mem_value;
            mem_write_32(op->mem_addr & ~3, val);
            break;
    }

    /* clear stage input and transfer to next stage */
    pipe.mem_op = NULL;
    pipe.wb_op = op;
}

void update_BTB(uint32_t PC, Pipe_Op *op){
    /* Updating the address tag*/
    branch_buffer[op->BTB_index].addr_tag = op->pc;
    branch_buffer[op->BTB_index].target = op->branch_dest;
    if(op->branch_dest >= 0x00400000 && op->branch_dest < 0x00500000){
        branch_buffer[op->BTB_index].valid = true;
    }
    else{
        branch_buffer[op->BTB_index].valid = false;
    }
    branch_buffer[op->BTB_index].conditional = op->branch_cond;
}

_Bool check_flush_pipe(Pipe_Op *op){ //if true, flush
    //check if predicted direction matches actual dir (eg. predict taken, but actually not taken)
    if (op->is_branch && op->branch_taken != op->predict_taken){
        // printf("Flush due to condition 1\n");
        return true;
    }
    if (op->is_branch && op->branch_taken && branch_buffer[op->BTB_index].target != op->branch_dest) {
        // printf("Flush due to condition 2\n");
        return true;
    }
    // case 3 - if BTB misses
    if (op->is_branch && op->BTB_miss == true){
        // printf("Flush due to condition 3\n");
        return true;
    }
    return false;
}

void pipe_stage_execute()
{
    /* if a multiply/divide is in progress, decrement cycles until value is ready */
    if (pipe.multiplier_stall > 0)
        pipe.multiplier_stall--;

    /* if downstream stall, return (and leave any input we had) */
    if (pipe.mem_op != NULL)
        return;

    /* if no op to execute, return */
    if (pipe.execute_op == NULL)
        return;

    /* grab op and read sources */
    Pipe_Op *op = pipe.execute_op;

    /* read register values, and check for bypass; stall if necessary */
    int stall = 0;
    if (op->reg_src1 != -1) {
        if (op->reg_src1 == 0)
            op->reg_src1_value = 0;
        else if (pipe.mem_op && pipe.mem_op->reg_dst == op->reg_src1) {
            if (!pipe.mem_op->reg_dst_value_ready)
                stall = 1;
            else
                op->reg_src1_value = pipe.mem_op->reg_dst_value;
        }
        else if (pipe.wb_op && pipe.wb_op->reg_dst == op->reg_src1) {
            op->reg_src1_value = pipe.wb_op->reg_dst_value;
        }
        else
            op->reg_src1_value = pipe.REGS[op->reg_src1];
    }
    if (op->reg_src2 != -1) {
        if (op->reg_src2 == 0)
            op->reg_src2_value = 0;
        else if (pipe.mem_op && pipe.mem_op->reg_dst == op->reg_src2) {
            if (!pipe.mem_op->reg_dst_value_ready)
                stall = 1;
            else
                op->reg_src2_value = pipe.mem_op->reg_dst_value;
        }
        else if (pipe.wb_op && pipe.wb_op->reg_dst == op->reg_src2) {
            op->reg_src2_value = pipe.wb_op->reg_dst_value;
        }
        else
            op->reg_src2_value = pipe.REGS[op->reg_src2];
    }

    /* if bypassing requires a stall (e.g. use immediately after load),
     * return without clearing stage input */
    if (stall) 
        return;

    /* execute the op */
    switch (op->opcode) {
        case OP_SPECIAL:
            op->reg_dst_value_ready = 1;
            switch (op->subop) {
                case SUBOP_SLL:
                    op->reg_dst_value = op->reg_src2_value << op->shamt;
                    break;
                case SUBOP_SLLV:
                    op->reg_dst_value = op->reg_src2_value << op->reg_src1_value;
                    break;
                case SUBOP_SRL:
                    op->reg_dst_value = op->reg_src2_value >> op->shamt;
                    break;
                case SUBOP_SRLV:
                    op->reg_dst_value = op->reg_src2_value >> op->reg_src1_value;
                    break;
                case SUBOP_SRA:
                    op->reg_dst_value = (int32_t)op->reg_src2_value >> op->shamt;
                    break;
                case SUBOP_SRAV:
                    op->reg_dst_value = (int32_t)op->reg_src2_value >> op->reg_src1_value;
                    break;
                case SUBOP_JR:
                case SUBOP_JALR:
                    op->reg_dst_value = op->pc + 4;
                    op->branch_dest = op->reg_src1_value;
                    op->branch_taken = 1;
                    break;

                case SUBOP_MULT:
                    {
                        /* we set a result value right away; however, we will
                         * model a stall if the program tries to read the value
                         * before it's ready (or overwrite HI/LO). Also, if
                         * another multiply comes down the pipe later, it will
                         * update the values and re-set the stall cycle count
                         * for a new operation.
                         */
                        int64_t val = (int64_t)((int32_t)op->reg_src1_value) * (int64_t)((int32_t)op->reg_src2_value);
                        uint64_t uval = (uint64_t)val;
                        pipe.HI = (uval >> 32) & 0xFFFFFFFF;
                        pipe.LO = (uval >>  0) & 0xFFFFFFFF;

                        /* four-cycle multiplier latency */
                        pipe.multiplier_stall = 4;
                    }
                    break;
                case SUBOP_MULTU:
                    {
                        uint64_t val = (uint64_t)op->reg_src1_value * (uint64_t)op->reg_src2_value;
                        pipe.HI = (val >> 32) & 0xFFFFFFFF;
                        pipe.LO = (val >>  0) & 0xFFFFFFFF;

                        /* four-cycle multiplier latency */
                        pipe.multiplier_stall = 4;
                    }
                    break;

                case SUBOP_DIV:
                    if (op->reg_src2_value != 0) {

                        int32_t val1 = (int32_t)op->reg_src1_value;
                        int32_t val2 = (int32_t)op->reg_src2_value;
                        int32_t div, mod;

                        div = val1 / val2;
                        mod = val1 % val2;

                        pipe.LO = div;
                        pipe.HI = mod;
                    } else {
                        // really this would be a div-by-0 exception
                        pipe.HI = pipe.LO = 0;
                    }

                    /* 32-cycle divider latency */
                    pipe.multiplier_stall = 32;
                    break;

                case SUBOP_DIVU:
                    if (op->reg_src2_value != 0) {
                        pipe.HI = (uint32_t)op->reg_src1_value % (uint32_t)op->reg_src2_value;
                        pipe.LO = (uint32_t)op->reg_src1_value / (uint32_t)op->reg_src2_value;
                    } else {
                        /* really this would be a div-by-0 exception */
                        pipe.HI = pipe.LO = 0;
                    }

                    /* 32-cycle divider latency */
                    pipe.multiplier_stall = 32;
                    break;

                case SUBOP_MFHI:
                    /* stall until value is ready */
                    if (pipe.multiplier_stall > 0)
                        return;

                    op->reg_dst_value = pipe.HI;
                    break;
                case SUBOP_MTHI:
                    /* stall to respect WAW dependence */
                    if (pipe.multiplier_stall > 0)
                        return;

                    pipe.HI = op->reg_src1_value;
                    break;

                case SUBOP_MFLO:
                    /* stall until value is ready */
                    if (pipe.multiplier_stall > 0)
                        return;

                    op->reg_dst_value = pipe.LO;
                    break;
                case SUBOP_MTLO:
                    /* stall to respect WAW dependence */
                    if (pipe.multiplier_stall > 0)
                        return;

                    pipe.LO = op->reg_src1_value;
                    break;

                case SUBOP_ADD:
                case SUBOP_ADDU:
                    op->reg_dst_value = op->reg_src1_value + op->reg_src2_value;
                    break;
                case SUBOP_SUB:
                case SUBOP_SUBU:
                    op->reg_dst_value = op->reg_src1_value - op->reg_src2_value;
                    break;
                case SUBOP_AND:
                    op->reg_dst_value = op->reg_src1_value & op->reg_src2_value;
                    break;
                case SUBOP_OR:
                    op->reg_dst_value = op->reg_src1_value | op->reg_src2_value;
                    break;
                case SUBOP_NOR:
                    op->reg_dst_value = ~(op->reg_src1_value | op->reg_src2_value);
                    break;
                case SUBOP_XOR:
                    op->reg_dst_value = op->reg_src1_value ^ op->reg_src2_value;
                    break;
                case SUBOP_SLT:
                    op->reg_dst_value = ((int32_t)op->reg_src1_value <
                            (int32_t)op->reg_src2_value) ? 1 : 0;
                    break;
                case SUBOP_SLTU:
                    op->reg_dst_value = (op->reg_src1_value < op->reg_src2_value) ? 1 : 0;
                    break;
            }
            break;

        case OP_BRSPEC:
            switch (op->subop) {
                case BROP_BLTZ:
                case BROP_BLTZAL:
                    if ((int32_t)op->reg_src1_value < 0) op->branch_taken = 1;
                    break;

                case BROP_BGEZ:
                case BROP_BGEZAL:
                    if ((int32_t)op->reg_src1_value >= 0) op->branch_taken = 1;
                    break;
            }
            break;

        case OP_BEQ:
            if (op->reg_src1_value == op->reg_src2_value) op->branch_taken = 1;
            break;

        case OP_BNE:
            if (op->reg_src1_value != op->reg_src2_value) op->branch_taken = 1;
            break;

        case OP_BLEZ:
            if ((int32_t)op->reg_src1_value <= 0) op->branch_taken = 1;
            break;

        case OP_BGTZ:
            if ((int32_t)op->reg_src1_value > 0) op->branch_taken = 1;
            break;

        case OP_ADDI:
        case OP_ADDIU:
            op->reg_dst_value_ready = 1;
            op->reg_dst_value = op->reg_src1_value + op->se_imm16;
            break;
        case OP_SLTI:
            op->reg_dst_value_ready = 1;
            op->reg_dst_value = (int32_t)op->reg_src1_value < (int32_t)op->se_imm16 ? 1 : 0;
            break;
        case OP_SLTIU:
            op->reg_dst_value_ready = 1;
            op->reg_dst_value = (uint32_t)op->reg_src1_value < (uint32_t)op->se_imm16 ? 1 : 0;
            break;
        case OP_ANDI:
            op->reg_dst_value_ready = 1;
            op->reg_dst_value = op->reg_src1_value & op->imm16;
            break;
        case OP_ORI:
            op->reg_dst_value_ready = 1;
            op->reg_dst_value = op->reg_src1_value | op->imm16;
            break;
        case OP_XORI:
            op->reg_dst_value_ready = 1;
            op->reg_dst_value = op->reg_src1_value ^ op->imm16;
            break;
        case OP_LUI:
            op->reg_dst_value_ready = 1;
            op->reg_dst_value = op->imm16 << 16;
            break;

        case OP_LW:
        case OP_LH:
        case OP_LHU:
        case OP_LB:
        case OP_LBU:
            op->mem_addr = op->reg_src1_value + op->se_imm16;
            break;

        case OP_SW:
        case OP_SH:
        case OP_SB:
            op->mem_addr = op->reg_src1_value + op->se_imm16;
            op->mem_value = op->reg_src2_value;
            break;
    }

    /* Update Branch Prediction*/
    if (op->branch_cond == true){
    /* 1. Updating PHT*/
        if (op->branch_taken == 1 && global_pattern[op->pattern_index].PHT_entry < 3){
            global_pattern[op->pattern_index].PHT_entry += 1;
        }
        if (op->branch_taken == 0 && global_pattern[op->pattern_index].PHT_entry > 0){
            global_pattern[op->pattern_index].PHT_entry -= 1;
        }
    /* 2. Updating GHR */
        GHR = (GHR << 1) | op->branch_taken;
    }

    if (op->is_branch){
    /* 3. Updating BTB */
        update_BTB(pipe.PC, op);
    }

    /* handle branch recoveries at this point */
    _Bool check_flush_return = check_flush_pipe(op);
    if (pipe.decode_op != 0){
        Pipe_Op *temp_pointer = pipe.decode_op;
        if(check_flush_return && pipe.instr_stall_state &&
            op->branch_dest == temp_pointer->pc){
            
            //backup stall count
            uint32_t instr_stall_cbackup = pipe.instr_stall_count;
            pipe_recover(3, op->branch_dest);
            pipe.instr_stall_count = instr_stall_cbackup;
            pipe.instr_stall_state = true;
        }
    }
    if(check_flush_return && op->branch_taken){
        //Actually flusing 3 stages
        pipe_recover(3, op->branch_dest);
    }
    else if(check_flush_return && !op->branch_taken)
    {
        pipe_recover(3, op->pc + 4);
    }

    /* remove from upstream stage and place in downstream stage */
    pipe.execute_op = NULL;
    pipe.mem_op = op;
}

void pipe_stage_decode()
{
    /* if downstream stall, return (and leave any input we had) */
    if (pipe.execute_op != NULL) // if the address pointed to by the pointer is NOT empty (it is still pointing to sth), return
        return;

    /* if no op to decode, return */
    if (pipe.decode_op == NULL)
        return;

    /* grab op and remove from stage input */
    Pipe_Op *op = pipe.decode_op;
    pipe.decode_op = NULL;

    /* set up info fields (source/dest regs, immediate, jump dest) as necessary */
    uint32_t opcode = (op->instruction >> 26) & 0x3F;
    uint32_t rs = (op->instruction >> 21) & 0x1F;
    uint32_t rt = (op->instruction >> 16) & 0x1F;
    uint32_t rd = (op->instruction >> 11) & 0x1F;
    uint32_t shamt = (op->instruction >> 6) & 0x1F;
    uint32_t funct1 = (op->instruction >> 0) & 0x1F;
    uint32_t funct2 = (op->instruction >> 0) & 0x3F;
    uint32_t imm16 = (op->instruction >> 0) & 0xFFFF;
    uint32_t se_imm16 = imm16 | ((imm16 & 0x8000) ? 0xFFFF8000 : 0);
    uint32_t targ = (op->instruction & ((1UL << 26) - 1)) << 2;

    op->opcode = opcode;
    op->imm16 = imm16;
    op->se_imm16 = se_imm16;
    op->shamt = shamt;

    switch (opcode) {
        case OP_SPECIAL:
            /* all "SPECIAL" insts are R-types that use the ALU and both source
             * regs. Set up source regs and immediate value. */
            op->reg_src1 = rs;
            op->reg_src2 = rt;
            op->reg_dst = rd;
            op->subop = funct2;
            if (funct2 == SUBOP_SYSCALL) {
                op->reg_src1 = 2; // v0
                op->reg_src2 = 3; // v1
            }
            if (funct2 == SUBOP_JR || funct2 == SUBOP_JALR) {
                op->is_branch = 1;
                op->branch_cond = 0;
            }

            break;

        case OP_BRSPEC:
            /* branches that have -and-link variants come here */
            op->is_branch = 1;
            op->reg_src1 = rs;
            op->reg_src2 = rt;
            op->is_branch = 1;
            op->branch_cond = 1; /* conditional branch */
            op->branch_dest = op->pc + 4 + (se_imm16 << 2);
            op->subop = rt;
            if (rt == BROP_BLTZAL || rt == BROP_BGEZAL) {
                /* link reg */
                op->reg_dst = 31;
                op->reg_dst_value = op->pc + 4;
                op->reg_dst_value_ready = 1;
            }
            break;

        case OP_JAL:
            op->reg_dst = 31;
            op->reg_dst_value = op->pc + 4;
            op->reg_dst_value_ready = 1;
            op->branch_taken = 1;
            /* fallthrough */
        case OP_J:
            op->is_branch = 1;
            op->branch_cond = 0;
            op->branch_taken = 1;
            op->branch_dest = (op->pc & 0xF0000000) | targ;
            break;

        case OP_BEQ:
        case OP_BNE:
        case OP_BLEZ:
        case OP_BGTZ:
            /* ordinary conditional branches (resolved after execute) */
            op->is_branch = 1;
            op->branch_cond = 1;
            op->branch_dest = op->pc + 4 + (se_imm16 << 2);
            op->reg_src1 = rs;
            op->reg_src2 = rt;
            break;

        case OP_ADDI:
        case OP_ADDIU:
        case OP_SLTI:
        case OP_SLTIU:
            /* I-type ALU ops with sign-extended immediates */
            op->reg_src1 = rs;
            op->reg_dst = rt;
            break;

        case OP_ANDI:
        case OP_ORI:
        case OP_XORI:
        case OP_LUI:
            /* I-type ALU ops with non-sign-extended immediates */
            op->reg_src1 = rs;
            op->reg_dst = rt;
            break;

        case OP_LW:
        case OP_LH:
        case OP_LHU:
        case OP_LB:
        case OP_LBU:
        case OP_SW:
        case OP_SH:
        case OP_SB:
            /* memory ops */
            op->is_mem = 1;
            op->reg_src1 = rs;
            if (opcode == OP_LW || opcode == OP_LH || opcode == OP_LHU || opcode == OP_LB || opcode == OP_LBU) {
                /* load */
                op->mem_write = 0;
                op->reg_dst = rt;
            }
            else {
                /* store */
                op->mem_write = 1;
                op->reg_src2 = rt;
            }
            break;
    }
    /* we will handle reg-read together with bypass in the execute stage */
    /* place op in downstream slot */
    pipe.execute_op = op;
}

uint32_t set_number;
uint32_t current_tag;

void update_recentness(int i){
    for (int k = 0; k < 4; k++){
        if (instr_cache[set_number][k].tag != 0){
            instr_cache[set_number][k].recentness += 1;
        }
    }
    instr_cache[set_number][i].recentness = 1; //Set that block's recency to 1, and the first slot to 1 (lower = newer)
}

_Bool check_instr_cache() //Returns true for cache miss or false for cache hit
{
    /* Loop through each cache block and all the 8 data points (4 bypte each) of each block */
    for (int i = 0; i < 4; i++){
        /* see if this cache array postion contains our instruction */
        if (instr_cache[set_number][i].tag == current_tag){ // Cache hit
            return false; //True if stall, false if no stall
        }
    }

    pipe.instr_stall_count = 50;
    if (pipe.data_stall_state == true && pipe.data_stall_count == 50) {
        pipe.instr_stall_count += 50;
    }
    return true; //cache miss (stall)
}

void store_instr_cache(){ //Takes in the PC value and store it into the appropriate position

    /* Case 1 - Cache Miss - when there is an empty block, store into the first empty slot (numerical order) for that block*/ 
    for (int i = 0; i < 4; i++){
        if (instr_cache[set_number][i].tag == 0){ //Empty block exists (tag is empty for that block)
            //store the data and tag into that block, and add recency to it
            instr_cache[set_number][i].tag = current_tag;
            update_recentness(i);
            return;
        }
    }

    //Case 2 - cache miss without any empty space left -replace the oldest (highest value) with this new PC
    uint32_t oldest_recency = 0;
    int oldest_position;

    //Find the oldest value, and store the corresponding block index
    for(int i = 0; i < 4; i++){
        if (oldest_recency < instr_cache[set_number][i].recentness){
            oldest_recency = instr_cache[set_number][i].recentness;
            oldest_position = i;
        }
    }

    instr_cache[set_number][oldest_position].tag = current_tag;
    update_recentness(oldest_position);
    return;
}

_Bool check_BTB_taken (Pipe_Op *op){
    /* check whether pipe.PC matches the tag, and also check the valid bit */
    if ((branch_buffer[op->BTB_index].valid == true && 
        branch_buffer[op->BTB_index].addr_tag == pipe.PC) || 
        branch_buffer[op->BTB_index].conditional == false){
        return true;
    }
    return false;
}

_Bool BTB_hit_check (Pipe_Op *op){
    //check if BTB hits or misses
    if (branch_buffer[op->BTB_index].addr_tag == pipe.PC || branch_buffer[op->BTB_index].valid == 1){
        return true; //BTB hit
    }
    else{
        return false;
    }
}

void pipe_stage_fetch()
{
    set_number = (pipe.PC >> 5) & 0x3F; //Extract only bits 5 to 10
    current_tag = (pipe.PC >> 11); // & 0x1FFFFF; //Extract bits 11 to 31
    
    /* check instr cache stall */
    if (pipe.instr_stall_state == true && pipe.instr_stall_count > 0){
        pipe.instr_stall_count -= 1;
    }

    if (pipe.instr_stall_state == false){
        pipe.instr_stall_state = check_instr_cache(); // accesses instr cache & store value without implementing delay 
    }

    if (pipe.instr_stall_count == 1){
        /* This branch would only be entered in the 50th (last stall) cycle */
        /* Store this pipe.pc into the designated cache block*/ // Might need to store PC from the first cycle if that changes
        store_instr_cache();
    }

    /* if pipeline is stalled (our output slot is not empty), return */
    if (pipe.decode_op != NULL)
        return;

    /* Allocate an op and send it down the pipeline. */
    Pipe_Op *op = malloc(sizeof(Pipe_Op));
    memset(op, 0, sizeof(Pipe_Op));
    op->reg_src1 = op->reg_src2 = op->reg_dst = -1;

    if (pipe.instr_stall_state == true && pipe.instr_stall_count != 0){
        return;
    }

    if (pipe.instr_stall_count == 0){
        /* Set stall state to false to check the cache again in the next cycle */
        pipe.instr_stall_state = false;
    }
    
    op->instruction = mem_read_32(pipe.PC);
    op->pc = pipe.PC;
    pipe.decode_op = op;

    /* Check Branch Prediction */
    uint8_t bits_2_to_9_PC = (pipe.PC >> 2) & 0xFF;

    op->pattern_index = bits_2_to_9_PC ^ GHR;
    op->BTB_index = (pipe.PC >> 2) & 0x3FF;
    op->predict_taken = false;

    op->BTB_miss = !BTB_hit_check(op);
    if (op->BTB_miss == false){
        if (global_pattern[op->pattern_index].PHT_entry >= 2 && check_BTB_taken(op) == true){
            op->predict_taken = true;
        }
        else{
            op->predict_taken = false;
        }
    }
    else{
        op->predict_taken = false;
    }
    
    if (op->predict_taken == false) {
        /* update PC */
        pipe.PC += 4;
    }
    else{
        // Get the target from BTB and apply that as the next pipe.PC
        pipe.PC = branch_buffer[op->BTB_index].target; 
    }
    stat_inst_fetch++;
}