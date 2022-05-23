const INES_TAG: [u8; 4] = [0x4E, 0x45, 0x53, 0x1A];

#[derive(Debug, PartialEq)]
pub enum Mirroring {
    VERTICAL,
    HORIZONTAL,
    FOUR_SCREEN,
}

pub struct Rom {
    pub prg_rom: Vec<u8>,
    pub chr_rom: Vec<u8>,
    pub mapper: u8,
    pub screen_mirroring: Mirroring,
}

impl Rom {
    pub fn new(raw: &Vec<u8>) -> Result<Rom, String> {
        if (raw[0..4] != INES_TAG) {
            return Err("File is not in iNES file format".to_string());
        }

        // Rest of implementation
    }
}

pub mod Test {
    use super::*;

    struct TestRom {
        header: Vec<u8>,
        trainer: Option<Vec<u8>>,
        pgp_rom: Vec<u8>,
        chr_rom: Vec<u8>,
    }

    fn create_rom() {}

    pub fn test_rom() {}

    // tests here
}
