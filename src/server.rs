use std::{io, thread};
use std::fs::File;
use std::path::Path;
use interprocess::local_socket::{LocalSocketListener, LocalSocketStream};
use crate::log::parser::Parser;
use crate::log::state::State;

pub fn main(listener: LocalSocketListener) {
    for (id, client) in listener.incoming().filter_map(|r| r.ok()).enumerate() {
        thread::spawn(move || handler(client, id));
    }
}

fn debug_handler(mut client: LocalSocketStream, id: usize) {
    let mut f = File::create(Path::new(format!("/tmp/z3-{}.log", id).as_str())).unwrap();
    io::copy(&mut client, &mut f).unwrap();
}

fn handler(client: LocalSocketStream, id: usize) {
    let mut parser = Parser::new(client, id);
    let mut state = State::new();
    while let (Some(entry), errs) = parser.fuzzy_next().unwrap() {
        for err in errs {
            println!("{:?}", err);
        }
        state.process(entry).unwrap();
    }
    println!("Client {} is done.", id)
}