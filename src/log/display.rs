use std::fmt::{Display, Formatter};
use num_bigint::BigUint;
use crate::log::state::*;
use crate::log::parser;

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Decl::None => write!(f, "_: ?"),
            Decl::Sort(sort) => write!(f, "_: {}", sort),
            Decl::Named { name, sort } => write!(f, "{}: {}", name, sort),
        }
    }
}

impl Display for Meaning {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Meaning::Rat(parser::Rat { pos, num, denom }) => {
                if *pos && denom == &BigUint::from(1u32) {
                    write!(f, "{}", num)?;
                } else {
                    write!(f, "(")?;
                    if !pos { write!(f, "-")?; }
                    write!(f, "{}", num)?;
                    if denom != &BigUint::from(1u32) { write!(f, "/{}", denom)?; }
                    write!(f, ")")?;
                }
            },
        }
        Ok(())
    }
}

pub enum Binding {
    Function,
    Infix(usize, String),
    Prefix(String),
    Postfix(String),
    Other(usize, Box<dyn FnOnce(&Vec<TermView>, &mut Formatter<'_>) -> std::fmt::Result>),
}

impl Binding {
    pub fn strength(&self) -> usize {
        match self {
            Binding::Function => 100,
            Binding::Postfix(_) => 90,
            Binding::Prefix(_) => 80,
            Binding::Infix(strength, _) => *strength,
            Binding::Other(strength, _) => *strength,
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum TermView {
    Meaning(Meaning),
    App { decl: String, args: Vec<TermView> },
    Proof { decl: String, premises: Vec<TermView>, conclusion: Box<TermView> },
    Lambda { name: String, decls: Vec<Decl>, patterns: Vec<TermView>, body: Box<TermView> },
    Quant { name: String, decls: Vec<Decl>, patterns: Vec<TermView>, body: Box<TermView> },
    Var(usize),
}

impl TermView {
    fn bind(&self, f: &mut Formatter<'_>, want_binding: usize) -> std::fmt::Result {
        if self.binding_strength() <= want_binding {
            write!(f, "{}", "(")?;
            self.render(f)?;
            write!(f, "{}", ")")?;
        } else {
            self.render(f)?;
        }
        Ok(())
    }

    fn op_binding(decl: &String, arg_count: usize) -> Binding {
        match decl.as_str() {
            "=>" => Binding::Infix(20, "⇒".into()),
            "ite" if arg_count == 3 => Binding::Other(20, Box::new(|args, f| {
                args[0].bind(f, 20)?;
                write!(f, " ? ")?;
                args[1].bind(f, 20)?;
                write!(f, " : ")?;
                args[2].bind(f, 19)?;
                Ok(())
            })),
            "or" => Binding::Infix(30, "∨".into()),
            "and" => Binding::Infix(40, "∧".into()),
            "xor" => Binding::Infix(50, "≠".into()),
            "=" => Binding::Infix(50, "=".into()),
            "<=" => Binding::Infix(60, "≤".into()),
            ">=" => Binding::Infix(60, "≥".into()),
            "<" => Binding::Infix(60, "<".into()),
            ">" => Binding::Infix(60, ">".into()),
            "+" => Binding::Infix(70, "+".into()),
            "-" if arg_count > 1 => Binding::Infix(70, "-".into()),
            "*" => Binding::Infix(80, "*".into()),
            "div" => Binding::Infix(80, "/".into()),
            "mod" => Binding::Infix(80, "%".into()),
            "not" => Binding::Prefix("¬".into()),
            "-" if arg_count == 1 => Binding::Prefix("-".into()),
            "abs" if arg_count == 1 => Binding::Other(100, Box::new(|args, f| {
                write!(f, "|")?;
                args[0].bind(f, 0)?;
                write!(f, "|")?;
                Ok(())
            })),
            "pattern" => Binding::Other(100, Box::new(|args, f| {
                write!(f, "{}", "{")?;
                if args.len() > 0 {
                    args[0].bind(f, 0)?;
                    for arg in &args[1..] {
                        write!(f, ", ")?;
                        arg.bind(f, 0)?;
                    }
                }
                write!(f, "{}", "}")?;
                Ok(())
            })),
            "true" => Binding::Function,
            "false" => Binding::Function,
            _ => Binding::Function,
        }
    }

    fn binding_strength(&self) -> usize {
        match self {
            TermView::Meaning(_) => Binding::Function.strength(),
            TermView::App { decl, args, .. } => TermView::op_binding(decl, args.len()).strength(),
            TermView::Proof { decl, .. } => 5,
            TermView::Lambda { .. } => 10,
            TermView::Quant { .. } => 10,
            TermView::Var(_) => Binding::Function.strength(),
        }
    }

    fn render(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TermView::Meaning(m) => write!(f, "{}", m)?,
            TermView::App { decl, args } => {
                match TermView::op_binding(decl, args.len()) {
                    Binding::Infix(strength, op) if args.len() > 1 => {
                        args[0].bind(f, strength)?;
                        for arg in &args[1..] {
                            write!(f, " {} ", op)?;
                            arg.bind(f, strength)?;
                        }
                    }
                    Binding::Prefix(op) if args.len() == 1 => {
                        write!(f, "{}", op)?;
                        args[0].bind(f, 79)?;
                    }
                    Binding::Postfix(op) if args.len() == 1 => {
                        args[0].bind(f, 89)?;
                        write!(f, "{}", op)?;
                    }
                    Binding::Other(_, func) => {
                        func(args, f)?;
                    }
                    Binding::Function | _ => {
                        write!(f, "{}", decl)?;
                        if args.len() > 0 {
                            write!(f, "(")?;
                            args[0].bind(f, 0)?;
                            for arg in &args[1..] {
                                write!(f, ", ")?;
                                arg.bind(f, 0)?;
                            }
                            write!(f, ")")?;
                        }
                    }
                }
            }
            TermView::Proof { decl, premises, conclusion } => {
                if !premises.is_empty() {
                    premises[0].bind(f, 5)?;
                    for premise in &premises[1..premises.len()] {
                        write!(f, ", ")?;
                        premise.bind(f, 5)?;
                    }
                }
                write!(f, " ({}) ⊢ ", decl)?;
                conclusion.bind(f, 5)?;
            }
            TermView::Lambda { name, decls, patterns, body } => {
                write!(f, "λ")?;
                if decls.len() > 0 {
                    write!(f, "{}", decls[0])?;
                    for decl in &decls[1..] {
                        write!(f, ", {}", decl)?;
                    }
                }

                for pattern in patterns {
                    write!(f, " ")?;
                    pattern.bind(f, 10)?;
                }

                write!(f, " :: ")?;

                body.bind(f, 9)?;
            },
            TermView::Quant { name, decls, patterns, body } => {
                write!(f, "∀")?;
                if decls.len() > 0 {
                    write!(f, "{}", decls[0])?;
                    for decl in &decls[1..] {
                        write!(f, ", {}", decl)?;
                    }
                }

                for pattern in patterns {
                    write!(f, " ")?;
                    pattern.bind(f, 10)?;
                }

                write!(f, " :: ")?;

                body.bind(f, 9)?;
            },
            TermView::Var(n) => write!(f, "?{}", *n)?,
        }
        Ok(())
    }
}

impl Display for TermView {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.render(f)
    }
}