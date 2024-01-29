use std::fs::File;
use std::io;
use std::io::{Read, Write};
use std::path::Path;
use std::str::FromStr;
use num_bigint::BigUint;
use utf8_read::{Char, Reader, StreamPosition};
use crate::log::lexer::Error::{Unexpected, UnexpectedEnd};

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Id {
    Num(BigUint),
    Qualified { family: String, num: BigUint },
    Family(String),
}

#[derive(Eq, PartialEq, Debug)]
pub enum Token {
    Entry(String),
    Symbol(String),
    Identifier(Id),
    Punct(char),
    Zero, // Num or Pointer
    Num(BigUint),
    Neg(BigUint),
    Pointer(String),
}

#[derive(Debug)]
pub enum Error {
    IO(io::Error),
    MalformedUtf8(StreamPosition, usize),
    Unexpected(char),
    UnexpectedEnd,
}

pub type Result<T> = core::result::Result<T, Error>;

impl From<utf8_read::Error> for Error {
    fn from(err: utf8_read::Error) -> Self {
        match err {
            utf8_read::Error::IoError(err) =>
                Error::IO(err),
            utf8_read::Error::MalformedUtf8(pos, size) =>
                Error::MalformedUtf8(pos, size),
        }
    }
}

pub struct Lexer<R: Read> {
    r: Reader<R>,
    lookahead: Option<char>,
    line: u32,
    id: usize,
    debug_out: File,
}

fn is_first_sym_char(c: char) -> bool {
    c.is_ascii_alphabetic() ||
        c == '~' || c == '!' || c == '@' || c == '$' || c == '%' ||
        c == '^' || c == '&' || c == '*' || c == '_' || c == '-' ||
        c == '+' || c == '=' || c == '<' || c == '>' || // c == '.' ||
        c == '?' || c == '/'
}

fn is_sym_char(c: char) -> bool {
    c.is_ascii_digit() || is_first_sym_char(c) ||
        c == '.' ||
        c == '[' || c == ']' || c == ';' // < false, but safe over-approximation.
}

impl<R: Read> Lexer<R> {
    pub fn new(r: R, id: usize) -> Self {
        let path = format!("/tmp/z3-{}.log", id);
        let debug_out = File::create(Path::new(path.as_str())).unwrap();
        Self { r: Reader::new(r).set_eof_on_no_data(true), lookahead: None, line: 1, id, debug_out }
    }

    fn peek(&mut self) -> Result<Option<char>> {
        if self.lookahead.is_none() {
            self.lookahead = Some(match self.r.next_char()? {
                Char::Eof => return Ok(None),
                Char::NoData => return Ok(None),
                Char::Char('\n') => {
                    self.line += 1;
                    if self.line % 100_000 == 0 {
                        println!("line {}", self.line);
                    }
                    '\n'
                },
                Char::Char(c) => c
            });
            self.debug_out.write(self.lookahead.unwrap().to_string().as_bytes()).unwrap();
            self.debug_out.flush().unwrap();
        }

        Ok(self.lookahead)
    }

    fn read_if<F: FnOnce(char) -> bool>(&mut self, condition: F) -> Result<Option<char>> {
        let c = self.peek()?;
        if let Some(c) = c {
            if condition(c) {
                self.lookahead = None;
                Ok(Some(c))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    fn expect<F: FnOnce(char) -> bool>(&mut self, condition: F) -> Result<char> {
        let c = self.peek()?;
        if let Some(c) = c {
            if condition(c) {
                self.lookahead = None;
                Ok(c)
            } else {
                Err(Unexpected(c))
            }
        } else {
            Err(UnexpectedEnd)
        }
    }

    fn skip_whitespace(&mut self) -> Result<()> {
        while self.read_if(|c| c.is_ascii_whitespace())?.is_some() {}
        Ok(())
    }

    pub fn next(&mut self) -> Result<Option<Token>> {
        self.skip_whitespace()?;

        match self.peek()? {
            None => Ok(None),
            Some('#') => Ok(Some(self.next_identifier()?)),
            Some('[') => Ok(Some(self.next_entry()?)),
            Some('|') => Ok(Some(self.next_quoted_symbol()?)),
            Some('-') => Ok(Some(self.next_minus_continuation()?)),
            Some(c) if is_first_sym_char(c) => Ok(Some(self.next_symbol_or_fam_identifier()?)),
            Some('0') => Ok(Some(self.next_zero_cont()?)),
            Some(c) if c.is_ascii_digit() => Ok(Some(self.next_num()?)),
            Some(c) => { self.expect(|d| d == c)?; Ok(Some(Token::Punct(c))) },
        }
    }

    pub fn fuzzy_next(&mut self) -> Result<Option<Token>> {
        let mut result = self.next();

        while match result {
            Ok(_) => false, // done
            Err(Error::UnexpectedEnd) => false, // unrecoverable
            Err(Error::Unexpected(_)) => true, // recover
            Err(Error::IO(_)) => false, // unrecoverable
            Err(Error::MalformedUtf8(_, _)) => true, // recover
        } {
            result = self.next();
        }

        result
    }

    fn read_delim(&mut self, left: char, right: char) -> Result<String> {
        self.expect(|c| c == left)?;

        let mut result = String::new();

        while let Some(c) = self.read_if(|c| c != right)? {
            result.push(c);
        }

        self.expect(|c| c == right)?;

        Ok(result)
    }

    fn next_identifier(&mut self) -> Result<Token> {
        self.expect(|c| c == '#')?;
        Ok(Token::Identifier(Id::Num(self.next_number()?)))
    }

    fn next_entry(&mut self) -> Result<Token> {
        Ok(Token::Entry(self.read_delim('[', ']')?))
    }

    fn next_quoted_symbol(&mut self) -> Result<Token> {
        Ok(Token::Symbol(self.read_delim('|', '|')?))
    }

    fn next_symbol_or_fam_identifier(&mut self) -> Result<Token> {
        let mut result = String::new();
        result.push(self.expect(|c| is_first_sym_char(c))?);
        while let Some(c) = self.read_if(|c| is_sym_char(c))? {
            result.push(c)
        }

        if let Some(c) = self.read_if(|c| c == '#')? {
            if self.peek()?.is_some_and(|c| c.is_ascii_digit()) {
                let num = self.next_number()?;
                Ok(Token::Identifier(Id::Qualified { family: result, num }))
            } else {
                Ok(Token::Identifier(Id::Family(result)))
            }
        } else {
            Ok(Token::Symbol(result))
        }
    }

    fn next_zero_cont(&mut self) -> Result<Token> {
        self.expect(|c| c == '0')?;
        match self.peek()? {
            None => Ok(Token::Zero),
            Some(c) if c.is_ascii_digit() => self.next_num(),
            Some('x') => {
                self.expect(|c| c == 'x')?;
                let mut result: String = "0x".into();
                while let Some(c) = self.read_if(|c| c.is_ascii_hexdigit())? {
                    result.push(c)
                }
                Ok(Token::Pointer(result))
            },
            Some(_) => Ok(Token::Zero),
        }
    }

    fn next_minus_continuation(&mut self) -> Result<Token> {
        self.expect(|c| c == '-')?;
        let mut all_numeric = true;
        let mut result: String = "-".into();
        while let Some(c) = self.read_if(|c| is_sym_char(c))? {
            result.push(c);
            all_numeric |= c.is_ascii_digit();
        }
        Ok(if all_numeric && result.len() >= 2 {
            Token::Neg(BigUint::from_str(&result[1..]).expect(&result))
        } else {
            Token::Symbol(result)
        })
    }

    fn next_num(&mut self) -> Result<Token> {
        self.next_number().map(Token::Num)
    }

    fn next_number(&mut self) -> Result<BigUint> {
        let mut result: BigUint = self.expect(|c| c.is_ascii_digit())?.to_digit(10).unwrap().into();
        while let Some(c) = self.read_if(|c| c.is_ascii_digit())? {
            result = result * 10u8 + c.to_digit(10).unwrap()
        }
        Ok(result)
    }
}