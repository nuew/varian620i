use std::{
    error::Error,
    fs::File,
    io::{BufReader, Read},
};
use varian620i::Varian620i;

fn main() -> Result<(), Box<dyn Error>> {
    let Some(file) = std::env::args_os().nth(1) else {
        let exe = std::env::args().next();
        eprintln!("Usage: {} <image.bin>", exe.unwrap_or("cargo run".into()));
        return Ok(());
    };

    let mut file = BufReader::new(File::open(file)?);
    let mut image = Vec::new();
    file.read_to_end(&mut image)?;
    let image = image
        .chunks_exact(std::mem::size_of::<u16>())
        .map(|chunk| u16::from_ne_bytes([chunk[0], chunk[1]]))
        .collect();

    let mut emu = Varian620i::<u16>::from_image(image);
    while emu.running() {
        emu.step()
    }
    println!("{:?}", emu);

    Ok(())
}
