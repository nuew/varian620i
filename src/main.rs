use std::{
    error::Error,
    fs::File,
    io::{BufReader, Read},
};
use varian620i::{instruction::Instruction, Varian620i, VarianError};

fn main() -> Result<(), Box<dyn Error>> {
    let Some(file) = std::env::args_os().nth(1) else {
        let exe = std::env::args().next();
        eprintln!("Usage: {} <image.bin>", exe.unwrap_or("cargo run".into()));
        return Ok(());
    };

    let mut file = BufReader::new(File::open(file)?);
    let mut image = Vec::new();
    file.read_to_end(&mut image)?;
    let image: Box<_> = image
        .chunks_exact(std::mem::size_of::<u16>())
        .map(|chunk| u16::from_ne_bytes([chunk[0], chunk[1]]))
        .collect();

    let mut index = 0;
    while index < image.len() {
        let mut doubleword = false;
        let insn = Instruction::decode(image[index], || {
            doubleword = true;
            image
                .get(index + 1)
                .copied()
                .ok_or(VarianError::InvalidAddressError)
        });

        if doubleword && index + 1 < image.len() {
            println!(
                "{:04x} | {:06o} {:5} | {:?}",
                index,
                image[index],
                image[index + 1],
                insn
            );
        } else {
            println!("{:04x} | {:06o}       | {:?}", index, image[index], insn);
        }

        index += if doubleword { 2 } else { 1 };
    }

    println!("\nRunning...\n");

    let mut emu = Varian620i::<u16>::from_image(image);
    while !emu.is_halted() {
        if let Err(e) = emu.step() {
            println!("Error: {}", e);
        }
    }
    println!("{:?}", emu);

    Ok(())
}
