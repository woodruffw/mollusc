use std::fs;

use anyhow::Result;
use clap::{App, Arg};
use llvm_bitstream::parser::StreamEntry;
use llvm_bitstream::Bitstream;

fn app<'a>() -> App<'a> {
    App::new(env!("CARGO_PKG_NAME"))
        .version(env!("CARGO_PKG_VERSION"))
        .about(env!("CARGO_PKG_DESCRIPTION"))
        .arg(
            Arg::new("input")
                .about("the bitstream input to dump")
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

    let (wrapper, bitstream) = Bitstream::from(&input)?;

    if let Some(wrapper) = wrapper {
        println!("Wrapper: {:#?}", wrapper);
    }

    println!("Entered bitstream; magic: {:#X}", bitstream.magic);

    let mut scope = 0;
    for entry in bitstream {
        match entry? {
            StreamEntry::SubBlock(block) => {
                println!("{}BLOCK {} {{", "\t".repeat(scope), block.block_id);
                scope += 1;
            }
            StreamEntry::EndBlock => {
                scope -= 1;
                println!("{}}}", "\t".repeat(scope));
            }
            StreamEntry::Record(record) => {
                println!(
                    "{}RECORD {{ code: {}, fields: {:?} }}",
                    "\t".repeat(scope),
                    record.code,
                    record.fields
                )
            }
        };
    }

    Ok(())
}
