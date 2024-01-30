#![allow(dead_code)]
#![allow(unused_variables)]

mod server;
mod client;
mod log;

use std::env;
use std::fs::File;
use std::path::Path;
use interprocess::local_socket::{LocalSocketListener, LocalSocketStream};
use crate::log::parser::Parser;
use crate::log::state::{Blame, Error, State, Term};

const SOCKET_NAME: &'static str = "z3-bench.socket";

fn read_file(path: &'static str) {
    let path = Path::new(path);
    let f = File::open(path).unwrap();

    let mut state = State::new();
    let mut parser = Parser::new(f, 1234);

    while let (Some(entry), errs) = parser.fuzzy_next().unwrap() {
        for err in errs {
            match err {
                log::parser::Error::UnexpectedToken(_) => {},
                err => println!("{:?}", err),
            }
        }
        match state.process(entry) {
            Ok(_) => {}
            Err(err) => {
                match err {
                    Error::TermWithoutBlame(term) => {
                        println!("This term does not have a blame:");
                        println!("{}", state.view_term(&term));

                        fn inner_blame(state: &State, term: &Term) {
                            match term {
                                Term::App { args, .. } => {
                                    for arg in args {
                                        let term = state.get(arg);
                                        match term.get_blame() {
                                            None => inner_blame(state, term),
                                            Some(blame) => {
                                                println!("Blame for {}", state.view_term(term));
                                                println!("  {:?}", blame);
                                                inner_blame(state, term);
                                            }
                                        }
                                    }
                                }
                                _ => {},
                            }
                        }

                        inner_blame(&state, &term);
                    }
                    other => println!("{:?}", other)
                }
                return
            },
        }
    }
}

#[allow(unreachable_code)]
fn main() {
    read_file("/home/pieter/vercors/z3-1.log");
    return;

    let path = env::temp_dir().join(Path::new(SOCKET_NAME));

    match env::args().nth(1) {
        Some(command) if command == "server" =>
            server::main(LocalSocketListener::bind(path.clone()).unwrap()),
        _ => client::main(LocalSocketStream::connect(path.clone()).unwrap()),
    }
}