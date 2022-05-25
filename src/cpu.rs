use crate::{
    bus::{Bus},
    opcodes,
};
use std::collections::HashMap;

bitflags! {
    /// # Status Register (P) http://wiki.nesdev.com/w/index.php/Status_flags
    ///
    ///  7 6 5 4 3 2 1 0
    ///  N V _ B D I Z C
    ///  | |   | | | | +--- Carry Flag
    ///  | |   | | | +----- Zero Flag
    ///  | |   | | +------- Interrupt Disable
    ///  | |   | +--------- Decimal Mode (not used on NES)
    ///  | |   +----------- Break Command
    ///  | +--------------- Overflow Flag
    ///  +----------------- Negative Flag
    ///
    pub struct CpuFlags: u8 {
        const CARRY             = 0b00000001;
        const ZERO              = 0b00000010;
        const INTERRUPT_DISABLE = 0b00000100;
        const DECIMAL_MODE      = 0b00001000;
        const BREAK             = 0b00010000;
        const BREAK2            = 0b00100000;
        const OVERFLOW          = 0b01000000;
        const NEGATIVE          = 0b10000000;
    }
}

const STACK: u16 = 0x0100;
const STACK_RESET: u8 = 0xFD;

pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: CpuFlags,
    pub program_counter: u16,
    pub stack_pointer: u8,
    bus: Bus,
}

pub trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | lo
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        let lo = (data & 0xff) as u8;
        let hi = (data >> 8) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }
}

impl Mem for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.bus.mem_read(addr)
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.bus.mem_write(addr, data)
    }
    fn mem_read_u16(&self, pos: u16) -> u16 {
        self.bus.mem_read_u16(pos)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        self.bus.mem_write_u16(pos, data)
    }
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

impl CPU {
    pub fn new(bus: Bus) -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: CpuFlags::from_bits_truncate(0b100100),
            program_counter: 0,
            stack_pointer: STACK_RESET,
            bus: bus,
        }
    }

    pub fn get_absolute_address(&self, mode: &AddressingMode, addr: u16) -> u16 {
        match mode {
            AddressingMode::ZeroPage => self.mem_read(addr) as u16,

            AddressingMode::Absolute => self.mem_read_u16(addr),

            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(addr);
                let addr = pos.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(addr);
                let addr = pos.wrapping_add(self.register_y) as u16;
                addr
            }

            AddressingMode::Absolute_X => {
                let base = self.mem_read_u16(addr);
                let addr = base.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                let base = self.mem_read_u16(addr);
                let addr = base.wrapping_add(self.register_y as u16);
                addr
            }

            AddressingMode::Indirect_X => {
                let base = self.mem_read(addr);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(addr);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }

            _ => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn set_register_a(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn add_to_register_a(&mut self, data: u8) {
        let mut carry_flag: u16 = 0;

        if self.status.contains(CpuFlags::CARRY) {
            carry_flag = 1;
        }

        let sum = self.register_a as u16 + data as u16 + carry_flag;

        let carry = sum > 0xff;

        // Set proper Carry Flag
        if carry {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        let result = sum as u8;

        // Set proper Overflow Flag
        if (data ^ result) & (result ^ self.register_a) & 0x80 != 0 {
            self.status.insert(CpuFlags::OVERFLOW);
        } else {
            self.status.remove(CpuFlags::OVERFLOW)
        }

        self.set_register_a(result);
    }

    fn stack_pop(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read((STACK as u16) + self.stack_pointer as u16)
    }

    fn stack_push(&mut self, data: u8) {
        self.mem_write((STACK as u16) + self.stack_pointer as u16, data);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }

    fn stack_push_u16(&mut self, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.stack_push(hi);
        self.stack_push(lo);
    }

    fn stack_pop_u16(&mut self) -> u16 {
        let lo = self.stack_pop() as u16;
        let hi = self.stack_pop() as u16;

        hi << 8 | lo
    }

    fn set_carry_flag(&mut self) {
        self.status.insert(CpuFlags::CARRY)
    }

    fn clear_carry_flag(&mut self) {
        self.status.remove(CpuFlags::CARRY)
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        if result == 0 {
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        if result & 0b1000_0000 != 0 {
            self.status.insert(CpuFlags::NEGATIVE);
        } else {
            self.status.remove(CpuFlags::NEGATIVE);
        }
    }

    fn branch(&mut self, condition: bool) {
        if condition {
            let jump: i8 = self.mem_read(self.program_counter) as i8;
            let jump_addr = self
                .program_counter
                .wrapping_add(1)
                .wrapping_add(jump as u16);

            self.program_counter = jump_addr;
        }
    }

    fn compare(&mut self, mode: &AddressingMode, compare_with: u8) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        if data <= compare_with {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        self.update_zero_and_negative_flags(compare_with.wrapping_sub(data));
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            _ => self.get_absolute_address(mode, self.program_counter),
        }
    }

    /*
        NES platform has a special mechanism to mark where the CPU should start the execution.
        Upon inserting a new cartridge, the CPU receives a special signal called "Reset interrupt" that instructs CPU to:
        1. reset the state (registers and flags)
        2. set program_counter to the 16-bit address that is stored at 0xFFFC
    */
    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.stack_pointer = STACK_RESET;
        self.status = CpuFlags::from_bits_truncate(0b100100);

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn load(&mut self, program: Vec<u8>) {
        for i in 0..(program.len() as u16) {
            self.mem_write(0x0600 + i, program[i as usize]);
        }
        //self.mem_write_u16(0xFFFC, 0x0600);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.program_counter = 0x0600;
        self.run()
    }

    pub fn run(&mut self) {
        self.run_with_callback(|_| {});
    }

    pub fn run_with_callback<F>(&mut self, mut callback: F)
    where
        F: FnMut(&mut CPU),
    {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODES_MAP;

        loop {
            callback(self);
            let current_code = self.mem_read(self.program_counter);
            self.program_counter += 1;
            let program_counter_state = self.program_counter;

            let opcode = opcodes
                .get(&current_code)
                .expect(&format!("OpCode {:x} is not recognized", current_code));

            match current_code {
                /* ADC */
                0x69 | 0x65 | 0x75 | 0x6D | 0x7D | 0x79 | 0x61 | 0x71 => {
                    self.adc(&opcode.mode);
                }

                /* AND */
                0x29 | 0x25 | 0x35 | 0x2D | 0x3D | 0x39 | 0x21 | 0x31 => {
                    self.and(&opcode.mode);
                }

                0x0A => self.asl_accumulator(),

                /* ASL */
                0x06 | 0x16 | 0x0E | 0x1E => {
                    self.asl(&opcode.mode);
                }

                /* BCC */
                0x90 => self.bcc(),

                /* BCS */
                0xB0 => self.bcs(),

                /* BEQ */
                0xF0 => self.beq(),

                /* BIT */
                0x24 | 0x2C => {
                    self.bit(&opcode.mode);
                }

                /* BMI */
                0x30 => self.bmi(),

                /* BNE */
                0xD0 => self.bne(),

                /* BPL */
                0x10 => self.bpl(),

                /* BRK */
                0x00 => return,

                /* BVC */
                0x50 => self.bvc(),

                /* BVS */
                0x70 => self.bvs(),

                /* CLC */
                0x18 => self.clear_carry_flag(),

                /* CLD */
                0xD8 => self.cld(),

                /* CLI */
                0x58 => self.cli(),

                /* CLV */
                0xB8 => self.clv(),

                /* CMP */
                0xC9 | 0xC5 | 0xD5 | 0xCD | 0xDD | 0xD9 | 0xC1 | 0xD1 => {
                    self.compare(&opcode.mode, self.register_a);
                }

                /* CPX */
                0xE0 | 0xE4 | 0xEC => {
                    self.compare(&opcode.mode, self.register_x);
                }

                /* CPY */
                0xC0 | 0xC4 | 0xCC => {
                    self.compare(&opcode.mode, self.register_y);
                }

                /* *DCP */
                0xC7 | 0xD7 | 0xCF | 0xDF | 0xDB | 0xD3 | 0xC3 => {
                    self.dcp(&opcode.mode);
                }

                /* DEC */
                0xC6 | 0xD6 | 0xCE | 0xDE => {
                    self.dec(&opcode.mode);
                }

                /* DEX */
                0xCA => self.dex(),

                /* DEY */
                0x88 => self.dey(),

                /* EOR */
                0x49 | 0x45 | 0x55 | 0x4D | 0x5D | 0x59 | 0x41 | 0x51 => {
                    self.eor(&opcode.mode);
                }

                /* INC */
                0xE6 | 0xF6 | 0xEE | 0xFE => {
                    self.inc(&opcode.mode);
                }

                /* INX */
                0xE8 => self.inx(),

                /* INY */
                0xC8 => self.iny(),

                /* JMP Absolute */
                0x4C => self.jmp_absolute(),

                /* JMP Indirect */
                0x6C => self.jmp_indirect(),

                /* JSR */
                0x20 => self.jsr(),

                /* *LAX */
                0xA7 | 0xB7 | 0xAF | 0xBF | 0xA3 | 0xB3 => {
                    // Shortcut for LDA value then TAX
                    self.lda(&opcode.mode);
                    self.tax(); // This might potentially not need the set carry 

                }

                /* LDA */
                0xA9 | 0xA5 | 0xB5 | 0xAD | 0xBD | 0xB9 | 0xA1 | 0xB1 => {
                    self.lda(&opcode.mode);
                }

                /* LDX */
                0xA2 | 0xA6 | 0xB6 | 0xAE | 0xBE => {
                    self.ldx(&opcode.mode);
                }

                /* LDY */
                0xA0 | 0xA4 | 0xB4 | 0xAC | 0xBC => {
                    self.ldy(&opcode.mode);
                }

                /* LSR */
                0x4A => self.lsr_accumulator(),
                0x46 | 0x56 | 0x4E | 0x5E => {
                    self.lsr(&opcode.mode);
                }

                /* NOP */
                0x1A | 0x3A | 0x5A | 0x7A | 0xDA | 0xEA | 0xFA => {
                    // do nothing
                }

                /* *NOP Read */
                0x04 | 0x44 | 0x64 | 0x0C | 0x1C | 0x3C | 
                0x5C | 0x7C | 0xDC | 0xFC | 0x14 | 0x34 | 
                0x54 | 0x74 | 0xD4 | 0xF4    => {
                    let addr = self.get_operand_address(&opcode.mode);
                    let data = self.mem_read(addr);
                    // Do nothing else
                }

                /* *NOP SKB */
                0x80 | 0x82 | 0x89 | 0xC2 | 0xE2 => {
                    /* 2 byte NOP (immidiate ), skip */
                }

                /* ORA */
                0x09 | 0x05 | 0x15 | 0x0D | 0x1D | 0x19 | 0x01 | 0x11 => {
                    self.ora(&opcode.mode);
                }

                /* PHA */
                0x48 => self.pha(),

                /* PHP */
                0x08 => self.php(),

                /* PLA */
                0x68 => self.pla(),

                /* PLP */
                0x28 => self.plp(),

                /* ROL */
                0x2A => self.rol_accumulator(),
                0x26 | 0x36 | 0x2E | 0x3E => {
                    self.rol(&opcode.mode);
                }

                /* ROR */
                0x6A => self.ror_accumulator(),
                0x66 | 0x76 | 0x6E | 0x7E => {
                    self.ror(&opcode.mode);
                }

                /* RTI */
                0x40 => self.rti(),

                /* RTS */
                0x60 => self.rts(),

                /* *SAX */
                0x83 | 0x87 | 0x8F | 0x97 => {
                    self.sax(&opcode.mode);
                }

                /* SBC */
                0xE9 | 0xE5 | 0xF5 | 0xED | 0xFD | 0xF9 | 0xE1 | 0xF1 | 0xEB => {
                    self.sbc(&opcode.mode);
                }

                /* SEC */
                0x38 => self.sec(),

                /* SED */
                0xF8 => self.sed(),

                /* SEI */
                0x78 => self.sei(),

                /* STA */
                0x85 | 0x95 | 0x8D | 0x9D | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }

                /* STX */
                0x86 | 0x96 | 0x8E => {
                    self.stx(&opcode.mode);
                }

                /* STY */
                0x84 | 0x94 | 0x8C => {
                    self.sty(&opcode.mode);
                }

                /* TAX */
                0xAA => self.tax(),

                /* TAY */
                0xA8 => self.tay(),

                /* TSX */
                0xBA => self.tsx(),

                /* TXA */
                0x8A => self.txa(),

                /* TXS */
                0x9A => self.txs(),

                /* TYA */
                0x98 => self.tya(),

                _ => todo!(""),
            }

            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }
        }
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.add_to_register_a(value);
    }

    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_a(value & self.register_a);
    }

    fn asl_accumulator(&mut self) {
        let mut data = self.register_a;
        if data >> 7 == 1 {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        data = data << 1;
        self.set_register_a(data)
    }

    fn asl(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        if data >> 7 == 1 {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        data = data << 1;
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn bcc(&mut self) {
        self.branch(!self.status.contains(CpuFlags::CARRY));
    }

    fn bcs(&mut self) {
        self.branch(self.status.contains(CpuFlags::CARRY));
    }

    fn beq(&mut self) {
        self.branch(self.status.contains(CpuFlags::ZERO));
    }

    fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        let and = self.register_a & data;
        if and == 0 {
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        self.status.set(CpuFlags::NEGATIVE, data & 0b10000000 > 0);
        self.status.set(CpuFlags::OVERFLOW, data & 0b01000000 > 0);
    }

    fn bmi(&mut self) {
        self.branch(self.status.contains(CpuFlags::NEGATIVE));
    }

    fn bne(&mut self) {
        self.branch(!self.status.contains(CpuFlags::ZERO));
    }

    fn bpl(&mut self) {
        self.branch(!self.status.contains(CpuFlags::NEGATIVE));
    }

    fn bvc(&mut self) {
        self.branch(!self.status.contains(CpuFlags::OVERFLOW));
    }

    fn bvs(&mut self) {
        self.branch(self.status.contains(CpuFlags::OVERFLOW));
    }

    fn cld(&mut self) {
        self.status.remove(CpuFlags::DECIMAL_MODE);
    }

    fn cli(&mut self) {
        self.status.remove(CpuFlags::INTERRUPT_DISABLE);
    }

    fn clv(&mut self) {
        self.status.remove(CpuFlags::OVERFLOW);
    }

    fn dcp(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        data = data.wrapping_sub(1);
        self.mem_write(addr, data);
        // self._update_zero_and_negative_flags(data);
        if data <= self.register_a {
            self.status.insert(CpuFlags::CARRY);
        }

        self.update_zero_and_negative_flags(self.register_a.wrapping_sub(data));
    }

    fn dec(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        data = data.wrapping_sub(1);
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        return data;
    }

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn eor(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);

        self.set_register_a(data ^ self.register_a);
    }

    fn inc(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        data = data.wrapping_add(1);
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        return data;
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.set_register_a(value);
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1); // u8 can only hold 0-255
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn iny(&mut self) {
        self.register_y = self.register_y.wrapping_add(1); // u8 can only hold 0-255
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn jmp_absolute(&mut self) {
        let mem_addr = self.mem_read_u16(self.program_counter);
        self.program_counter = mem_addr;
    }

    fn jmp_indirect(&mut self) {
        let mem_addr = self.mem_read_u16(self.program_counter);
        // let indirect_ref = self.mem_read_u16(mem_address);
        //6502 bug mode with with page boundary:
        //  if address $3000 contains $40, $30FF contains $80, and $3100 contains $50,
        // the result of JMP ($30FF) will be a transfer of control to $4080 rather than $5080 as you intended
        // i.e. the 6502 took the low byte of the address from $30FF and the high byte from $3000

        let indirect_ref = if mem_addr & 0x00FF == 0x00FF {
            let lo = self.mem_read(mem_addr);
            let hi = self.mem_read(mem_addr & 0xFF00);
            (hi as u16) << 8 | (lo as u16)
        } else {
            self.mem_read_u16(mem_addr)
        };

        self.program_counter = indirect_ref;
    }

    fn jsr(&mut self) {
        self.stack_push_u16(self.program_counter + 2 - 1);
        let target_address = self.mem_read_u16(self.program_counter);
        self.program_counter = target_address
    }

    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.register_x = data;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.register_y = data;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn lsr_accumulator(&mut self) {
        let mut data = self.register_a;
        if data & 1 == 1 {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        data = data >> 1;
        self.set_register_a(data)
    }

    fn lsr(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        if data & 1 == 1 {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        data = data >> 1;
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn ora(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.set_register_a(data | self.register_a);
    }

    fn pha(&mut self) {
        self.stack_push(self.register_a);
    }

    fn php(&mut self) {
        //http://wiki.nesdev.com/w/index.php/CPU_status_flag_behavior
        let mut flags = self.status.clone();
        flags.insert(CpuFlags::BREAK);
        flags.insert(CpuFlags::BREAK2);
        self.stack_push(flags.bits());
    }

    fn pla(&mut self) {
        let data = self.stack_pop();
        self.set_register_a(data);
    }

    fn plp(&mut self) {
        self.status.bits = self.stack_pop();
        self.status.remove(CpuFlags::BREAK);
        self.status.insert(CpuFlags::BREAK2);
    }

    fn rol(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data >> 7 == 1 {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        data = data << 1;
        if old_carry {
            data = data | 1;
        }
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn rol_accumulator(&mut self) {
        let mut data = self.register_a;
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data >> 7 == 1 {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        data = data << 1;
        if old_carry {
            data = data | 1;
        }
        self.set_register_a(data);
    }

    fn ror(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data & 1 == 1 {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        data = data >> 1;
        if old_carry {
            data = data | 0b10000000;
        }
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn ror_accumulator(&mut self) {
        let mut data = self.register_a;
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data & 1 == 1 {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        data = data >> 1;
        if old_carry {
            data = data | 0b10000000;
        }
        self.set_register_a(data);
    }

    fn rti(&mut self) {
        self.status.bits = self.stack_pop();
        self.status.remove(CpuFlags::BREAK);
        self.status.insert(CpuFlags::BREAK2);

        self.program_counter = self.stack_pop_u16();
    }

    fn rts(&mut self) {
        self.program_counter = self.stack_pop_u16() + 1;
    }

    fn sax(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.register_a & self.register_x;
        self.mem_write(addr, data);
    }

    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.add_to_register_a(((data as i8).wrapping_neg().wrapping_sub(1)) as u8);
    }

    fn sec(&mut self) {
        self.status.insert(CpuFlags::CARRY);
    }

    fn sed(&mut self) {
        self.status.insert(CpuFlags::DECIMAL_MODE);
    }

    fn sei(&mut self) {
        self.status.insert(CpuFlags::INTERRUPT_DISABLE);
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn stx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_x)
    }

    fn sty(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_y)
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn tay(&mut self) {
        self.register_y = self.register_a;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn tsx(&mut self) {
        self.register_x = self.stack_pointer;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn txa(&mut self) {
        self.register_a = self.register_x;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn txs(&mut self) {
        self.stack_pointer = self.register_x;
    }

    fn tya(&mut self) {
        self.register_a = self.register_y;
        self.update_zero_and_negative_flags(self.register_a);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cartridge::test;

    #[test]
    fn test_0xa9_lda_immidiate_load_data() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);

        assert_eq!(cpu.register_a, 0x05);
        assert!(cpu.status.bits() & 0b0000_0010 == 0b00);
        assert!(cpu.status.bits() & 0b1000_0000 == 0);
    }

    #[test]
    fn test_0xa9_lda_zero_flag() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);

        assert!(cpu.status.bits() & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_0xaa_tax_move_a_to_x() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0x0a, 0xaa, 0x00]);

        assert_eq!(cpu.register_x, 10);
    }

    #[test]
    fn test_5_ops_working_together() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_inx_overflow() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0xff, 0xaa, 0xe8, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    fn test_lda_from_memory() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0x55);

        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_nop() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0x55);

        cpu.load_and_run(vec![0xEA, 0x00]);

        assert_eq!(cpu.register_a, 0x00);
    }

    #[test]
    fn test_tye() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0x55);
        cpu.load_and_run(vec![0xa5, 0x10, 0x98, 0x00]);

        assert_eq!(cpu.register_a, cpu.register_y)
    }
}
