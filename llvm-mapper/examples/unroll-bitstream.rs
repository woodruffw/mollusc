use std::convert::TryFrom;
use std::fs;

use anyhow::Result;
use clap::{App, Arg};
use llvm_bitstream::Bitstream;
use llvm_mapper::unroll::Bitcode;

fn app<'a>() -> App<'a> {
    App::new(env!("CARGO_PKG_NAME"))
        .version(env!("CARGO_PKG_VERSION"))
        .about(env!("CARGO_PKG_DESCRIPTION"))
        .arg(
            Arg::new("input")
                .help("the bitstream input to unroll")
                .index(1)
                .required(true),
        )
}

fn main() -> Result<()> {
    env_logger::init();
    let matches = app().get_matches();

    let input = {
        let input = matches.value_of("input").unwrap();
        fs::read(input)?
    };

    let (_, bitstream) = Bitstream::from(&input)?;

    let unrolled = Bitcode::try_from(bitstream)?;
    println!("{:#?}", unrolled);

    Ok(())
}
