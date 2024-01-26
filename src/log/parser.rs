use std::io;
use crate::log::lexer::{Id, Lexer, Token};
use std::io::Read;
use num_bigint::{BigInt, BigUint};
use num_traits::cast::ToPrimitive;
use utf8_read::StreamPosition;
use crate::log::lexer;
use crate::log::lexer::Token::{Identifier, Neg, Num, Pointer, Punct, Symbol};
use crate::log::parser::Entry::{AttachVarNames, MkLambda, MkQuant, MkVar};
use crate::log::parser::Error::{StarEmpty};

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Decl {
    pub name: Option<String>,
    pub sort: String,
}

pub struct SNum {
    pub pos: bool,
    pub num: BigUint,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Rat {
    pub pos: bool,
    pub num: BigUint,
    pub denom: BigUint,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Meaning {
    Rat(Rat),
    // TODO: ANum
    // TODO: BV
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Substitution {
    None(Id),
    Sub { original: Id, substituted: Id },
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum EqExpl {
    Root,
    Literal { equality: Id, id: Id },
    Axiom(Id),
    CongruenceOrCommutativity { args: Vec<Substitution>, id: Id },
    Theory { name: String, id: Id },
    Unknown(Id),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Literal {
    True,
    False,
    Pos(Id),
    Neg(Id),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum SatLiteral {
    Null,
    Pos(u64),
    Neg(u64),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Justification {
    Axiom,
    Binary(SatLiteral),
    Clause(Vec<SatLiteral>),
    Justification { theory: i64, literals: Vec<SatLiteral> },
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Entry {
    ToolVersion(u64, u64, u64),
    MkApp { id: Id, decl: String, args: Vec<Id> },
    MkProof { id: Id, decl: String, premises: Vec<Id>, conclusion: Id },
    MkLambda { id: Id, name: String, decls: usize, patterns: Vec<Id>, body: Id },
    MkQuant { id: Id, name: String, decls: usize, patterns: Vec<Id>, body: Id },
    MkVar { id: Id, offset: usize },
    AttachVarNames { id: Id, decls: Vec<Decl> },
    AttachMeaning { id: Id, family: String, meaning: Meaning },
    NewMatch { ptr: String, id: Id, pattern: Id, bindings: Vec<Id>, blame: Vec<Substitution>, },
    EqExpl { id: Id, explanation: EqExpl, },
    TheoryInstanceDiscovered { ptr: String, axiom: Id, bindings: Vec<Id>, blame: Vec<Id> },
    MbqiInstanceDiscovered { ptr: String, id: Id, bindings: Vec<Id> },
    Instance { ptr: String, proof: Option<Id>, generation: Option<u64> },
    EndOfInstance,
    AttachEnode { id: Id, generation: u64 },
    DecideAndOr(Id, Id),
    ResolveLiteral { conflict_level: u64, literal: Literal },
    ResolveProcess(Literal),
    BeginCheck(u64),
    Push(u64),
    Pop { scopes: u64, scope_level: u64 },
    Conflict(Vec<Literal>),
    Assign { literal: Literal, decision: bool, justification: Justification },
    Eof,
}

pub type Result<T> = core::result::Result<T, Error>;

#[derive(Debug)]
pub enum Error {
    IO(io::Error),
    MalformedUtf8(StreamPosition, usize),
    UnexpectedCharacter(char),
    UnexpectedToken(Token),
    UnexpectedEnd,
    Unexpected,
    StarEmpty,
    NumRange(BigUint),
    InumRange(BigInt),
}

impl From<lexer::Error> for Error {
    fn from(err: lexer::Error) -> Self {
        match err {
            lexer::Error::IO(err) => Error::IO(err),
            lexer::Error::MalformedUtf8(pos, len) => Error::MalformedUtf8(pos, len),
            lexer::Error::Unexpected(c) => Error::UnexpectedCharacter(c),
            lexer::Error::UnexpectedEnd => Error::UnexpectedEnd,
        }
    }
}

pub struct Parser<R: Read> {
    lexer: Lexer<R>,
    lookahead: Option<Token>,
    id: usize,
}

impl<R: Read> Parser<R> {
    pub fn new(r: R, id: usize) -> Self {
        Self::from_lexer(Lexer::new(r, id), id)
    }

    pub fn from_lexer(lexer: Lexer<R>, id: usize) -> Self {
        Self { lexer, lookahead: None, id }
    }

    fn peek(&mut self) -> Result<&Option<Token>> {
        if self.lookahead.is_none() {
            self.lookahead = self.lexer.next()?
        }

        Ok(&self.lookahead)
    }

    fn read_if<F: FnOnce(&Token) -> bool>(&mut self, condition: F) -> Result<Option<Token>> {
        if let Some(token) = self.peek()? {
            if condition(token) {
                Ok(self.lookahead.take())
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    fn read_with<T, F: FnOnce(Token) -> core::result::Result<T, Token>>(&mut self, f: F) -> Result<Option<T>> {
        self.peek()?;
        let maybe_token = self.lookahead.take();
        match maybe_token {
            None => Ok(None),
            Some(token) => match f(token) {
                Err(r) => { self.lookahead = Some(r); Ok(None) },
                Ok(t) => Ok(Some(t)),
            }
        }
    }

    fn star<T, F: Fn(Token) -> core::result::Result<T, Token>>(&mut self, f: F) -> Result<Vec<T>> {
        let mut result = Vec::<T>::new();
        while let Some(t) = self.read_with(&f)? {
            result.push(t)
        }
        Ok(result)
    }

    fn expect<F: FnOnce(&Token) -> bool>(&mut self, condition: F) -> Result<Token> {
        self.peek()?;
        match self.lookahead.take() {
            None => Err(Error::UnexpectedEnd),
            Some(token) =>
                if condition(&token) { Ok(token) }
                else { Err(Error::UnexpectedToken(token)) },
        }
    }

    fn expect_str(&mut self, s: &str) -> Result<()> {
        self.expect(|tok| tok == &Symbol(s.into())).map(|_| ())
    }

    fn expect_punct(&mut self, c: char) -> Result<()> {
        self.expect(|tok| tok == &Punct(c)).map(|_| ())
    }

    fn expect_num(&mut self) -> Result<BigUint> {
        self.peek()?;
        match self.lookahead.take() {
            None => Err(Error::UnexpectedEnd),
            Some(Token::Zero) => Ok(0u8.into()),
            Some(Num(n)) => Ok(n),
            Some(other) => Err(Error::UnexpectedToken(other)),
        }
    }

    fn expect_inum(&mut self) -> Result<BigInt> {
        self.peek()?;
        match self.lookahead.take() {
            None => Err(Error::UnexpectedEnd),
            Some(Token::Zero) => Ok(0u8.into()),
            Some(Num(n)) => Ok(n.into()),
            Some(Neg(n)) => Ok(-BigInt::from(n)),
            Some(other) => Err(Error::UnexpectedToken(other))
        }
    }

    fn expect_u64(&mut self) -> Result<u64> {
        let n = self.expect_num()?;
        n.to_u64().ok_or(Error::NumRange(n))
    }

    fn expect_usize(&mut self) -> Result<usize> {
        let n = self.expect_num()?;
        n.to_usize().ok_or(Error::NumRange(n))
    }

    fn expect_id(&mut self) -> Result<Id> {
        self.peek()?;
        match self.lookahead.take() {
            None => Err(Error::UnexpectedEnd),
            Some(Identifier(id)) => Ok(id),
            Some(other) => Err(Error::UnexpectedToken(other)),
        }
    }

    fn expect_ids(&mut self) -> Result<Vec<Id>> {
        self.star(|tok| match tok {
            Identifier(id) => Ok(id),
            tok => Err(tok),
        })
    }

    fn expect_symbol(&mut self) -> Result<String> {
        self.peek()?;
        match self.lookahead.take() {
            None => Err(Error::UnexpectedEnd),
            Some(Symbol(s)) => Ok(s),
            Some(other) => Err(Error::UnexpectedToken(other)),
        }
    }

    fn expect_pointer(&mut self) -> Result<String> {
        self.peek()?;
        match self.lookahead.take() {
            None => Err(Error::UnexpectedEnd),
            Some(Token::Zero) => Ok("nullptr".into()),
            Some(Pointer(s)) => Ok(s),
            Some(other) => Err(Error::UnexpectedToken(other)),
        }
    }

    fn star_decl(&mut self) -> Result<Vec<Decl>> {
        let mut result = vec![];
        while let Some(_) = self.read_if(|tok| tok == &Punct('('))? {
            let name = self.read_with(|tok| match tok {
                Symbol(s) => Ok(s),
                tok => Err(tok),
            })?;
            self.expect_punct(';')?;
            let sort = self.expect_symbol()?;
            self.expect_punct(')')?;
            result.push(Decl { name, sort });
        }
        Ok(result)
    }

    fn expect_snum(&mut self) -> Result<SNum> {
        self.peek()?;
        match self.lookahead.take() {
            None => Err(Error::UnexpectedEnd),
            Some(Token::Zero) => Ok(SNum { pos: true, num: 0u64.into() }),
            Some(Num(n)) => Ok(SNum { pos: true, num: n }),
            Some(Punct('(')) => {
                self.expect_str("-")?;
                let n = self.expect_num()?;
                self.expect_punct(')')?;
                Ok(SNum { pos: false, num: n })
            },
            Some(tok) => Err(Error::UnexpectedToken(tok))
        }
    }

    fn expect_rat(&mut self) -> Result<Rat> {
        self.peek()?;
        match self.lookahead.take() {
            None => Err(Error::UnexpectedEnd),
            Some(Token::Zero) => Ok(Rat { pos: true, num: 0u64.into(), denom: 1u64.into() }),
            Some(Num(n)) => Ok(Rat { pos: true, num: n, denom: 1u64.into() }),
            Some(Punct('(')) => {
                self.peek()?;
                match self.lookahead.take() {
                    None => Err(Error::UnexpectedEnd),
                    Some(Symbol(s)) if s.as_str() == "-" => {
                        let n = self.expect_num()?;
                        self.expect_punct(')')?;
                        Ok(Rat { pos: false, num: n, denom: 1u64.into() })
                    }
                    Some(Symbol(s)) if s.as_str() == "/" => {
                        let num = self.expect_snum()?;
                        let denom = self.expect_snum()?;
                        self.expect_punct(')')?;
                        Ok(Rat { pos: num.pos ^ denom.pos, num: num.num, denom: denom.num })
                    }
                    Some(tok) => Err(Error::UnexpectedToken(tok))
                }
            },
            Some(tok) => Err(Error::UnexpectedToken(tok))
        }
    }

    fn expect_meaning(&mut self) -> Result<Meaning> {
        self.expect_rat().map(Meaning::Rat)
    }

    fn expect_substitutions(&mut self) -> Result<Vec<Substitution>> {
        let mut result = vec![];
        loop {
            let tok = self.read_if(|tok| match tok {
                Identifier(_) => true,
                Punct('(') => true,
                _ => false,
            })?;

            match tok {
                None => return Ok(result),
                Some(Identifier(id)) => result.push(Substitution::None(id)),
                Some(Punct('(')) => {
                    let original = self.expect_id()?;
                    let substituted = self.expect_id()?;
                    self.expect_punct(')')?;
                    result.push(Substitution::Sub { original, substituted });
                },
                _ => unreachable!(),
            }
        }
    }

    fn expect_eq_expl(&mut self) -> Result<EqExpl> {
        let kind = self.expect_symbol()?;
        match kind.as_str() {
            "root" => Ok(EqExpl::Root),
            "lit" => {
                let id1 = self.expect_id()?;
                self.expect_punct(';')?;
                let id2 = self.expect_id()?;
                Ok(EqExpl::Literal { equality: id1, id: id2 })
            },
            "ax" => {
                self.expect_punct(';')?;
                let id = self.expect_id()?;
                Ok(EqExpl::Axiom(id))
            },
            "cg" => {
                let args = self.expect_substitutions()?;
                self.expect_punct(';')?;
                let id = self.expect_id()?;
                Ok(EqExpl::CongruenceOrCommutativity { args, id })
            },
            "th" => {
                let name = self.expect_symbol()?;
                self.expect_punct(';')?;
                let id = self.expect_id()?;
                Ok(EqExpl::Theory { name, id })
            },
            "unknown" => {
                self.expect_punct(';')?;
                let id = self.expect_id()?;
                Ok(EqExpl::Unknown(id))
            },
            _ => Err(Error::UnexpectedToken(Symbol(kind))),
        }
    }

    fn expect_literal(&mut self) -> Result<Literal> {
        let tok = self.expect(|_| true)?;
        match tok {
            Symbol(s) if s.as_str() == "true" => Ok(Literal::True),
            Symbol(s) if s.as_str() == "false" => Ok(Literal::False),
            Identifier(id) => Ok(Literal::Pos(id)),
            Punct('(') => {
                self.expect_str("not")?;
                let id = self.expect_id()?;
                self.expect_punct(')')?;
                Ok(Literal::Neg(id))
            },
            tok => Err(Error::UnexpectedToken(tok)),
        }
    }

    fn expect_literals(&mut self) -> Result<Vec<Literal>> {
        let mut result = vec![];
        loop {
            let cont = match self.peek()? {
                None => false,
                Some(tok) => match tok {
                    Symbol(s) if s.as_str() == "true" || s.as_str() == "false" => true,
                    Identifier(_) | Punct('(') => true,
                    _ => false,
                },
            };

            if cont { result.push(self.expect_literal()?) }
            else { return Ok(result) }
        }
    }

    fn read_sat_literal(&mut self) -> Result<Option<SatLiteral>> {
        let tok = self.read_if(|tok| match tok {
            Symbol(s) if s.as_str() == "null" => true,
            Token::Zero => true,
            Num(_) => true,
            Neg(_) => true,
            _ => false,
        })?;

        match tok {
            None => Ok(None),
            Some(Symbol(_)) => Ok(Some(SatLiteral::Null)),
            Some(Token::Zero) => Ok(Some(SatLiteral::Pos(0u64))),
            Some(Num(n)) => match n.to_u64() {
                None => Err(Error::UnexpectedToken(Num(n))),
                Some(n) => Ok(Some(SatLiteral::Pos(n))),
            },
            Some(Neg(n)) => match n.to_u64() {
                None => Err(Error::UnexpectedToken(Neg(n))),
                Some(n) => Ok(Some(SatLiteral::Neg(n))),
            }
            Some(_) => unreachable!(),
        }
    }

    fn expect_sat_literal(&mut self) -> Result<SatLiteral> {
        match self.read_sat_literal() {
            Err(e) => Err(e),
            Ok(None) => Err(Error::Unexpected),
            Ok(Some(literal)) => Ok(literal),
        }
    }

    fn star_sat_literal(&mut self) -> Result<Vec<SatLiteral>> {
        let mut result = vec![];
        while let Some(literal) = self.read_sat_literal()? {
            result.push(literal)
        }
        Ok(result)
    }

    fn expect_justification(&mut self) -> Result<Justification> {
        let kind = self.expect_symbol()?;

        match kind.as_str() {
            "axiom" => Ok(Justification::Axiom),
            "bin" => Ok(Justification::Binary(self.expect_sat_literal()?)),
            "clause" => Ok(Justification::Clause(self.star_sat_literal()?)),
            "justification" => {
                let unknown = self.read_if(|tok| tok == &Symbol("-1".into()))?.is_some();
                let theory = if unknown { -1 } else {
                    let theory = self.expect_inum()?;
                    match theory.to_i64() {
                        None => return Err(Error::InumRange(theory)),
                        Some(i) => i
                    }
                };
                self.expect_punct(':')?;
                let literals = self.star_sat_literal()?;
                Ok(Justification::Justification { theory, literals })
            },
            _ => Err(Error::UnexpectedToken(Symbol(kind))),
        }
    }

    pub fn next(&mut self) -> Result<Option<Entry>> {
        let entry = self.read_if(|_| true)?;
        match entry {
            None => Ok(None),
            Some(Token::Entry(entry)) => Ok(Some(self.next_entry(entry)?)),
            Some(tok) => Err(Error::UnexpectedToken(tok)),
        }
    }

    pub fn fuzzy_next(&mut self) -> Result<(Option<Entry>, Vec<Error>)> {
        let mut result = self.next();
        let mut errs = vec![];

        while match result {
            Ok(_) => false, // done
            Err(Error::UnexpectedEnd) => false, // unrecoverable
            Err(Error::IO(_)) => false, // unrecoverable
            Err(Error::MalformedUtf8(_, _)) => true, // recover
            Err(Error::UnexpectedCharacter(_)) => true, // recover
            Err(Error::UnexpectedToken(_)) => true, // recover
            Err(Error::Unexpected) => true, // recover
            Err(StarEmpty) => true, // recover
            Err(Error::NumRange(_)) => true, // recover
            Err(Error::InumRange(_)) => true, // recover
        } {
            errs.push(result.unwrap_err());
            result = self.next();
        }

        result.map(|entry| (entry, errs))
    }

    fn next_entry(&mut self, entry: String) -> Result<Entry> {
        match entry.as_str() {
            "tool-version" => self.next_tool_version(),
            "mk-proof" => self.next_proof(),
            "mk-app" => self.next_app(),
            "mk-lambda" => self.next_lambda(),
            "mk-quant" => self.next_quant(),
            "mk-var" => self.next_var(),
            "attach-var-names" => self.next_attach_var_names(),
            "attach-meaning" => self.next_attach_meaning(),
            "inst-discovered" => self.next_inst_discovered(),
            "instance" => self.next_instance(),
            "new-match" => self.next_new_match(),
            "eq-expl" => self.next_eq_expl(),
            "end-of-instance" => self.next_end_of_instance(),
            "attach-enode" => self.next_attach_enode(),
            "decide-and-or" => self.next_decide_and_or(),
            "resolve-lit" => self.next_resolve_lit(),
            "resolve-process" => self.next_resolve_process(),
            "begin-check" => self.next_begin_check(),
            "push" => self.next_push(),
            "pop" => self.next_pop(),
            "conflict" => self.next_conflict(),
            "assign" => self.next_assign(),
            "eof" => self.next_eof(),
            _ => Err(Error::UnexpectedToken(Token::Entry(entry))),
        }
    }

    fn next_tool_version(&mut self) -> Result<Entry> {
        self.expect_str("Z3")?;
        let v1 = self.expect_u64()?;
        self.expect_punct('.')?;
        let v2 = self.expect_u64()?;
        self.expect_punct('.')?;
        let v3 = self.expect_u64()?;
        Ok(Entry::ToolVersion(v1, v2 as u64, v3 as u64))
    }

    fn next_proof(&mut self) -> Result<Entry> {
        let id = self.expect_id()?;
        let decl = self.expect_symbol()?;
        let mut args = self.expect_ids()?;
        let conclusion = args.pop().ok_or(Error::StarEmpty)?;
        Ok(Entry::MkProof { id, decl, premises: args, conclusion })
    }

    fn next_app(&mut self) -> Result<Entry> {
        let id = self.expect_id()?;
        let decl = self.expect_symbol()?;
        let args = self.expect_ids()?;
        Ok(Entry::MkApp { id, decl, args })
    }

    fn next_lambda(&mut self) -> Result<Entry> {
        let id = self.expect_id()?;
        let name = self.expect_symbol()?;
        let decls = self.expect_usize()?;
        let mut patterns_and_body = self.expect_ids()?;
        let body = patterns_and_body.pop().ok_or(StarEmpty)?;
        Ok(MkLambda { id, name, decls, patterns: patterns_and_body, body })
    }

    fn next_quant(&mut self) -> Result<Entry> {
        let id = self.expect_id()?;
        let name = self.expect_symbol()?;
        let decls = self.expect_usize()?;
        let mut patterns_and_body = self.expect_ids()?;
        let body = patterns_and_body.pop().ok_or(StarEmpty)?;
        Ok(MkQuant { id, name, decls, patterns: patterns_and_body, body })
    }

    fn next_var(&mut self) -> Result<Entry> {
        Ok(MkVar {
            id: self.expect_id()?,
            offset: self.expect_usize()?,
        })
    }

    fn next_attach_var_names(&mut self) -> Result<Entry> {
        Ok(AttachVarNames {
            id: self.expect_id()?,
            decls: self.star_decl()?,
        })
    }

    fn next_attach_meaning(&mut self) -> Result<Entry> {
        let id = self.expect_id()?;
        let family = self.expect_symbol()?;
        let meaning = self.expect_meaning()?;
        Ok(Entry::AttachMeaning { id, family, meaning })
    }

    fn next_inst_discovered(&mut self) -> Result<Entry> {
        match self.expect_symbol()?.as_str() {
            "theory-solving" => self.next_theory_solving(),
            "MBQI" => self.next_mbqi(),
            _ => Err(Error::Unexpected),
        }
    }

    fn next_theory_solving(&mut self) -> Result<Entry> {
        let ptr = self.expect_pointer()?;
        let axiom = self.expect_id()?;
        let bindings = self.expect_ids()?;
        let have_semi = self.read_if(|c| c == &Punct(';'))?.is_some();
        let blame = if have_semi { self.expect_ids()? } else { vec![] };
        Ok(Entry::TheoryInstanceDiscovered { ptr, axiom, bindings, blame })
    }

    fn next_mbqi(&mut self) -> Result<Entry> {
        let ptr = self.expect_pointer()?;
        let id = self.expect_id()?;
        let bindings = self.expect_ids()?;
        Ok(Entry::MbqiInstanceDiscovered { ptr, id, bindings })
    }

    fn next_instance(&mut self) -> Result<Entry> {
        let ptr = self.expect_pointer()?;
        let proof = self.read_with(|tok| match tok {
            Identifier(id) => Ok(id),
            tok => Err(tok),
        })?;
        let have_semi = self.read_if(|tok| tok == &Punct(';'))?.is_some();
        let generation = if have_semi { Some(self.expect_u64()?) } else { None };
        Ok(Entry::Instance { ptr, proof, generation })
    }

    fn next_new_match(&mut self) -> Result<Entry> {
        let ptr = self.expect_pointer()?;
        let id = self.expect_id()?;
        let pattern = self.expect_id()?;
        let bindings = self.expect_ids()?;
        self.expect_punct(';')?;
        let blame = self.expect_substitutions()?;
        Ok(Entry::NewMatch { ptr, id, pattern, bindings, blame })
    }

    fn next_eq_expl(&mut self) -> Result<Entry> {
        let id = self.expect_id()?;
        let explanation = self.expect_eq_expl()?;
        Ok(Entry::EqExpl { id, explanation })
    }

    fn next_end_of_instance(&mut self) -> Result<Entry> {
        Ok(Entry::EndOfInstance)
    }

    fn next_attach_enode(&mut self) -> Result<Entry> {
        let id = self.expect_id()?;
        let generation = self.expect_u64()?;
        Ok(Entry::AttachEnode { id, generation })
    }

    fn next_decide_and_or(&mut self) -> Result<Entry> {
        let id1 = self.expect_id()?;
        let id2 = self.expect_id()?;
        Ok(Entry::DecideAndOr(id1, id2))
    }

    fn next_resolve_lit(&mut self) -> Result<Entry> {
        let conflict_level = self.expect_u64()?;
        let literal = self.expect_literal()?;
        Ok(Entry::ResolveLiteral { conflict_level, literal })
    }

    fn next_resolve_process(&mut self) -> Result<Entry> {
        Ok(Entry::ResolveProcess(self.expect_literal()?))
    }

    fn next_begin_check(&mut self) -> Result<Entry> {
        Ok(Entry::BeginCheck(self.expect_u64()?))
    }

    fn next_push(&mut self) -> Result<Entry> {
        Ok(Entry::Push(self.expect_u64()?))
    }

    fn next_pop(&mut self) -> Result<Entry> {
        Ok(Entry::Pop { scopes: self.expect_u64()?, scope_level: self.expect_u64()? })
    }

    fn next_conflict(&mut self) -> Result<Entry> {
        let literals = self.expect_literals()?;
        Ok(Entry::Conflict(literals))
    }

    fn next_assign(&mut self) -> Result<Entry> {
        let literal = self.expect_literal()?;
        let decision = self.read_if(|tok| tok == &Symbol("decision".into()))?.is_some();
        let justification = self.expect_justification()?;
        Ok(Entry::Assign { literal, decision, justification })
    }

    fn next_eof(&mut self) -> Result<Entry> {
        Ok(Entry::Eof)
    }
}