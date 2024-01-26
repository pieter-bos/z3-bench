use std::{io, thread};
use std::fs::File;
use std::process::{Command, Stdio};
use interprocess::local_socket::{LocalSocketStream};
use interprocess::os::unix::fifo_file::create_fifo;
use tempfile::tempdir;

pub fn main(mut client: LocalSocketStream) {
    // Make a fifo to stand in for z3.log, and pipe it to the server
    let loc = tempdir().unwrap();
    let path = loc.into_path().join("z3.log");
    create_fifo(&path, 0o777).unwrap();

    // Pass the z3.log socket to z3
    let trace_file_arg = format!("trace_file_name={}", &path.to_str().unwrap());

    let io = thread::spawn(move || {
        let mut f = File::open(&path).unwrap();
        io::copy(&mut f, &mut client).unwrap();
    });

    Command::new("/home/pieter/z3/cmake-build-debug/z3")
        .args(["-smt2", "-in", "trace=true", "proof=true", trace_file_arg.as_str()])
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn().unwrap().wait().unwrap();

    io.join().unwrap();
}