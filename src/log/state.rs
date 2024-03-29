use std::collections::HashMap;
use std::iter;
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use crate::log::{lexer, parser};
use crate::log::parser::{Entry};
use crate::log::display::*;

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Error {
    NoSuchId(lexer::Id),
    InsertRange(BigUint),
    MeaningNotForApp(Meaning, Term),
    BlameNotForApp(Blame, Term),
    InstantiationNotForQuant(Term),
    EqExplNotForApp(EqExpl, Term),
    ReverseMonoNotForApp(Id, Term),
    VarNamesNotForBinder(Vec<Decl>, Term),
    DuplicateInstance(Instantiation, Instantiation),
    NoSuchInstance(String),
    NestedCurrentInstance(Instantiation, Instantiation),
    NoCurrentInstance,
    WrongProofShape(Term),
    TermWithoutBlame(Term),
}

pub type Result<T> = core::result::Result<T, Error>;

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Id {
    Num(usize),
    Qualified(String, usize),
    Family(String),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Decl {
    None,
    Sort(String),
    Named { name: String, sort: String },
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Meaning {
    Rat(parser::Rat),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Substitution {
    None(Id),
    Sub(Id, Id),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Instantiation {
    body: Option<Id>,
    bindings: Vec<Id>,
    inst: InstantiationKind,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum InstantiationKind {
    Match(MatchInstantiation),
    Theory(TheoryInstantiation),
    Model(ModelInstantiation),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct MatchInstantiation {
    quantifier: Id,
    pattern: Id,
    blame: Vec<Substitution>,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct TheoryInstantiation {
    family: lexer::Id,
    blame: Vec<Id>,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ModelInstantiation {
    quantifier: Id,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Blame {
    Assertion,
    Instantiation(Instantiation),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Meta {
    meaning: Option<Meaning>,
    blame: Option<Blame>,
    eq_expl: Option<EqExpl>,
    reverse_monotonicity: Option<Id>,
}

impl Meta {
    fn new() -> Self {
        Self { meaning: None, blame: None, eq_expl: None, reverse_monotonicity: None }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Term {
    App { decl: String, args: Vec<Id>, meta: Option<Box<Meta>> },
    Proof { decl: String, premises: Vec<Id>, conclusion: Id },
    Lambda { name: String, decls: Vec<Decl>, patterns: Vec<Id>, body: Id },
    Quant { name: String, decls: Vec<Decl>, patterns: Vec<Id>, body: Id },
    Var(usize),
}

impl Term {
    fn get_meaning(&self) -> &Option<Meaning> {
        match self {
            Term::App { meta, .. } => match meta {
                None => &None,
                Some(meta) => &meta.meaning
            }
            _ => &None,
        }
    }

    fn set_meaning(&mut self, meaning: Meaning) -> Result<()> {
        match self {
            Term::App { meta, .. } => {
                meta.get_or_insert_with(|| Box::new(Meta::new())).meaning = Some(meaning);
                Ok(())
            }
            _ => Err(Error::MeaningNotForApp(meaning, self.clone())),
        }
    }

    pub(crate) fn get_blame(&self) -> &Option<Blame> {
        match self {
            Term::App { meta, .. } => match meta {
                None => &None,
                Some(meta) => &meta.blame,
            }
            _ => &None,
        }
    }

    fn set_blame(&mut self, blame: Blame) -> Result<()> {
        match self {
            Term::App { meta, .. } => {
                meta.get_or_insert_with(|| Box::new(Meta::new())).blame = Some(blame);
                Ok(())
            }
            _ => Err(Error::BlameNotForApp(blame, self.clone())),
        }
    }

    fn get_eq_expl(&self) -> &Option<EqExpl> {
        match self {
            Term::App { meta, .. } => match meta {
                None => &None,
                Some(meta) => &meta.eq_expl,
            }
            _ => &None,
        }
    }

    fn set_eq_expl(&mut self, eq_expl: EqExpl) -> Result<()> {
        match self {
            Term::App { meta, .. } => {
                meta.get_or_insert_with(|| Box::new(Meta::new())).eq_expl = Some(eq_expl);
                Ok(())
            }
            _ => Err(Error::EqExplNotForApp(eq_expl, self.clone())),
        }
    }

    pub fn get_reverse_monotonicity(&self) -> &Option<Id> {
        match self {
            Term::App { meta, .. } => match meta {
                None => &None,
                Some(meta) => &meta.reverse_monotonicity,
            }
            _ => &None,
        }
    }

    fn set_reverse_monotonicity(&mut self, from: Id) -> Result<()> {
        match self {
            Term::App { meta, .. } => {
                meta.get_or_insert_with(|| Box::new(Meta::new())).reverse_monotonicity = Some(from);
                Ok(())
            }
            _ => Err(Error::ReverseMonoNotForApp(from, self.clone())),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum EqExpl {
    Root,
    Literal { equality: Id, id: Id },
    Axiom(Id),
    CongruenceOrCommutativity { args: Vec<Substitution>, id: Id },
    Theory { name: String, id: Id },
    Unknown(Id),
    ProofOfRewrite { id: Id },
    ProofOfCongruence { args: Vec<Substitution>, id: Id },
}

pub struct State {
    num_terms: Vec<Option<Term>>,
    qualified_terms: HashMap<String, Vec<Option<Term>>>,
    family_terms: HashMap<String, Term>,

    pending_instances: HashMap<String, Instantiation>,
    current_instance: Vec<Instantiation>,
    floating_enodes: Vec<Id>,

    eq_expl: HashMap<Id, EqExpl>,
}

impl State {
    pub fn new() -> Self {
        Self {
            num_terms: Vec::new(),
            qualified_terms: HashMap::new(),
            family_terms: HashMap::new(),
            pending_instances: HashMap::new(),
            current_instance: Vec::new(),
            floating_enodes: Vec::new(),
            eq_expl: HashMap::new(),
        }
    }

    pub(crate) fn get(&self, id: &Id) -> &Term {
        match id {
            Id::Num(n) => self.num_terms[*n].as_ref().unwrap(),
            Id::Qualified(family, n) => self.qualified_terms[family][*n].as_ref().unwrap(),
            Id::Family(family) => &self.family_terms[family],
        }
    }

    fn terms_contain_term(&self, haystacks: &Vec<Id>, needle: &Id) -> bool {
        for haystack in haystacks {
            if haystack == needle {
                return true
            }
        }

        for haystack in haystacks {
            if self.term_contains_term(haystack, needle) {
                return true
            }
        }

        false
    }
    fn term_contains_term(&self, haystack: &Id, needle: &Id) -> bool {
        if haystack == needle {
            return true
        }

        match self.get(haystack) {
            Term::App { args, .. } => self.terms_contain_term(args, needle),
            Term::Proof { conclusion, .. } => self.term_contains_term(conclusion, needle),
            Term::Lambda { body, .. } => self.term_contains_term(body, needle),
            Term::Quant { body, .. } => self.term_contains_term(body, needle),
            Term::Var(_) => false,
        }
    }

    fn get_mut(&mut self, id: &Id) -> &mut Term {
        match id {
            Id::Num(n) => self.num_terms[*n].as_mut().unwrap(),
            Id::Qualified(family, n) => self.qualified_terms.get_mut(family).unwrap()[*n].as_mut().unwrap(),
            Id::Family(family) => self.family_terms.get_mut(family).unwrap(),
        }
    }

    fn set_blame_recursive(&mut self, id: &Id, blame: Blame) {
        match self.get_mut(id) {
            Term::App { meta, args, .. } => {
                meta.get_or_insert_with(|| Box::new(Meta::new())).blame = Some(blame.clone());
                for arg in args.clone() {
                    self.set_blame_recursive(&arg, blame.clone());
                }
            },
            _ => {},
        }
    }

    pub fn view_id(&self, id: &Id) -> TermView {
        self.view_term(self.get(id))
    }

    fn view_ids(&self, ids: &Vec<Id>) -> Vec<TermView> {
        ids.iter().map(|id| self.view_id(id)).collect()
    }

    pub fn view_term(&self, term: &Term) -> TermView {
        match term {
            term if term.get_meaning().is_some() =>
                TermView::Meaning(term.get_meaning().clone().unwrap()),
            Term::App { decl, args, .. } =>
                TermView::App { decl: decl.clone(), args: self.view_ids(args) },
            Term::Proof { decl, premises, conclusion } =>
                TermView::Proof {
                    decl: decl.clone(),
                    premises: self.view_ids(premises),
                    conclusion: Box::new(self.view_id(conclusion)),
                },
            Term::Lambda { name, decls, patterns, body } =>
                TermView::Lambda {
                    name: name.clone(),
                    decls: decls.clone(),
                    patterns: self.view_ids(patterns),
                    body: Box::new(self.view_id(body)),
                },
            Term::Quant { name, decls, patterns, body } =>
                TermView::Quant {
                    name: name.clone(),
                    decls: decls.clone(),
                    patterns: self.view_ids(patterns),
                    body: Box::new(self.view_id(body)),
                },
            Term::Var(n) => TermView::Var(*n),
        }
    }

    fn new_id(&self, id: lexer::Id) -> Result<Id> {
        match id.clone() {
            lexer::Id::Num(n) => {
                let n = n.to_usize().ok_or(Error::NoSuchId(id.clone()))?;
                if let Some(Some(_)) = self.num_terms.get(n) {
                    Ok(Id::Num(n))
                } else {
                    return Err(Error::NoSuchId(id.clone()));
                }
            },
            lexer::Id::Qualified { family, num } => {
                let n = num.to_usize().ok_or(Error::NoSuchId(id.clone()))?;
                if self.qualified_terms.contains_key(&family) {
                    if let Some(Some(_)) = self.qualified_terms[&family].get(n) {
                        Ok(Id::Qualified(family, n))
                    } else { Err(Error::NoSuchId(id.clone())) }
                } else { Err(Error::NoSuchId(id.clone())) }
            },
            lexer::Id::Family(family) => {
                if self.family_terms.contains_key(&family) { Ok(Id::Family(family)) } else { Err(Error::NoSuchId(id.clone())) }
            },
        }
    }

    fn new_ids(&self, ids: Vec<lexer::Id>) -> Result<Vec<Id>> {
        ids.into_iter().map(|id| self.new_id(id)).collect::<Result<Vec<Id>>>()
    }

    fn new_substitution(&self, sub: parser::Substitution) -> Result<Substitution> {
        Ok(match sub {
            parser::Substitution::None(root) => Substitution::None(self.new_id(root)?),
            parser::Substitution::Sub { original, substituted } =>
                Substitution::Sub(self.new_id(original)?, self.new_id(substituted)?),
        })
    }

    fn new_substitutions(&self, subs: Vec<parser::Substitution>) -> Result<Vec<Substitution>> {
        // When a top term (Sub::None) has a blame, and does not occur in the body induced by it,
        // try to follow reverse monotonicity steps for that term and add a (Sub::Sub) for that
        // replacement. The new top term should be the found top term that occurs in the body of
        // the blamed instantiation.
        let mut result: Vec<Substitution> = Vec::new();
        for sub in subs.into_iter() {
            match sub {
                parser::Substitution::None(top_id) => {
                    let mut top_id = self.new_id(top_id)?;
                    let top_term = self.get(&top_id);
                    let blame = top_term.get_blame();
                    match blame {
                        Some(Blame::Instantiation(Instantiation { body: Some(body), .. })) => {
                            while !self.term_contains_term(body, &top_id) {
                                println!(">>>> Replacing {}", self.view_id(&top_id));
                                match self.get(&top_id).get_reverse_monotonicity().as_ref() {
                                    None => break,
                                    Some(id) => top_id = id.clone(),
                                }
                            }
                        },
                        _ => {},
                    }
                    result.push(Substitution::None(top_id));
                }
                sub => result.push(self.new_substitution(sub)?),
            }
        }
        Ok(result)
        // subs.into_iter().map(|sub| self.new_substitution(sub)).collect::<Result<Vec<Substitution>>>()
    }

    fn insert(&mut self, id: lexer::Id, term: Term) -> Result<()> {
        match &term {
            Term::Proof { decl, conclusion, .. } if decl.as_str() == "asserted" => {
                // println!("assert {}", self.view_id(&conclusion));
            }
            _ => {}
        }

        match id {
            lexer::Id::Num(n) => {
                let n = n.to_usize().ok_or(Error::InsertRange(n))?;
                if self.num_terms.len() <= n { self.num_terms.resize(n + 1, None); }
                self.num_terms[n] = Some(term);
            }
            lexer::Id::Qualified { family, num } => {
                if !self.qualified_terms.contains_key(&family) {
                    self.qualified_terms.insert(family.clone(), vec![]);
                }
                let terms = self.qualified_terms.get_mut(&family).unwrap();
                let n = num.to_usize().ok_or(Error::InsertRange(num))?;
                if terms.len() <= n { terms.resize(n + 1, None); }
                terms[n] = Some(term);
            }
            lexer::Id::Family(family) => {
                self.family_terms.insert(family, term);
            }
        }
        Ok(())
    }

    fn print_bindings(&self, quantifier: &Id, bindings: &Vec<Id>, indent: &String) -> Result<()> {
        println!("{}with bindings:", indent);
        if let Term::Quant { decls, .. } = self.get(quantifier) {
            for (decl, binding) in decls.iter().zip(bindings) {
                println!("{}{} = {}", indent, decl, self.view_id(binding));
            }
            Ok(())
        } else {
            Err(Error::InstantiationNotForQuant(self.get(quantifier).clone()))
        }
    }

    fn explain_term(&self, term: &Id, indent_size: usize) -> Result<()> {
        let indent = "  ".repeat(indent_size);
        println!("{}{}", indent, self.view_id(term));
        match self.get(term).get_blame() {
            None => {
                println!("{}rev-mono = {:?}", indent, self.get(term).get_reverse_monotonicity());
                return Err(Error::TermWithoutBlame(self.get(term).clone()))
                // return Ok(())
            },
            Some(blame) => {
                match blame {
                    Blame::Assertion => println!("{}(from assertion)", indent),
                    Blame::Instantiation(inst) => {
                        println!("{}from instantiation:", indent);
                        self.explain_inst(inst, indent_size+1)?;
                    },
                }
                Ok(())
            }
        }
    }

    fn explain_equality(&self, left: &Id, eq_expl: &EqExpl, right: &Id, indent_size: usize) -> Result<()> {
        let indent: String = "  ".repeat(indent_size);

        match eq_expl {
            EqExpl::Root => {
                println!("{}It is the root node in the E-graph", indent);
            }
            EqExpl::Literal { id, .. } | EqExpl::ProofOfRewrite { id } => {
                println!("{}They are directly proven equal", indent);
            }
            EqExpl::Axiom(_) => {
                println!("{}(proof generation disabled)", indent);
            }
            EqExpl::CongruenceOrCommutativity { args, id } | EqExpl::ProofOfCongruence { args, id } => {
                let Term::App { decl: left_f, .. } = self.get(left) else { todo!() };
                let Term::App { decl: right_f, .. } = self.get(right) else { todo!() };
                assert!(left_f == right_f);
                println!("{}Both terms apply {}, and their arguments are equal:", indent, left_f);
                for sub in args {
                    self.explain_substitution(sub, indent_size+1)?;
                }
            }
            EqExpl::Theory { name, id } => {
                println!("{}Theory {} deems it so", indent, name);
            }
            EqExpl::Unknown(_) => {
                println!("{}An unknown theory solver deems it so", indent);
            }
        }

        Ok(())
    }

    fn explain_substitution(&self, sub: &Substitution, indent_size: usize) -> Result<()> {
        let indent = "  ".repeat(indent_size);

        match sub {
            Substitution::None(root) => {
                println!("{}top level pattern term:", indent);
                self.explain_term(root, indent_size+1)?
            },
            Substitution::Sub(here, for_pat) => {
                let eq_expl = self.get(here).get_eq_expl().as_ref().unwrap();
                let eq_expl_pat = self.get(for_pat).get_eq_expl().as_ref().unwrap();

                if here == for_pat {
                    println!("{}matching substitution:", indent);
                    self.explain_term(here, indent_size+1)?;
                } else {
                    println!("{}replacing:", indent);
                    self.explain_term(here, indent_size+1)?;
                    println!("{}with:", indent);
                    self.explain_term(for_pat, indent_size+1)?;
                }

                println!("{}substitution allowed because:", indent);
                self.explain_equality(here, eq_expl, for_pat, indent_size+1)?;
            }
        }

        Ok(())
    }

    fn explain_inst(&self, inst: &Instantiation, indent_size: usize) -> Result<()> {
        let indent: String = "  ".repeat(indent_size);

        let body = &inst.body;
        let bindings = &inst.bindings;
        let inst = &inst.inst;

        match inst {
            InstantiationKind::Match(MatchInstantiation { quantifier, pattern, blame }) => {
                println!("{}{}", indent, self.view_id(quantifier));
                self.print_bindings(quantifier, bindings, &indent)?;
                println!("{}pattern: {}", indent, self.view_id(pattern));

                for sub in blame {
                    self.explain_substitution(sub, indent_size)?;
                }
            }
            InstantiationKind::Theory(TheoryInstantiation { family, blame }) => {
                if let Some(body) = body.as_ref() {
                    println!("from theory {:?}: {}", family, self.view_id(body));
                } else {
                    println!("from theory {:?}: ??", family);
                }

                for sub in blame {
                    self.explain_substitution(&Substitution::None(sub.clone()), indent_size)?;
                }
                // println!("{}(theory instantiation)", indent)
            }
            InstantiationKind::Model(ModelInstantiation { quantifier }) => {
                println!("{}model instantiation:", indent);
                println!("{}{}", indent, self.view_id(quantifier));
                self.print_bindings(quantifier, bindings, &indent)?;
            }
        }

        Ok(())
    }

    fn insert_instantiation(&mut self, ptr: String, inst: Instantiation) -> Result<()> {
        match self.pending_instances.insert(ptr.clone(), inst.clone()) {
            None => Ok(()),
            Some(other) => {
                // OK for now: this can happen when pending matches are discarded due to a pop.
                Ok(())
                /*
                println!("{}", ptr);
                Err(Error::DuplicateInstance(other, self.pending_instances.get(&ptr).unwrap().clone()))
                */
            },
        }
    }

    fn proof_rewrite_blame(&mut self, premises: &Vec<Id>, conclusion: &Id) -> Result<()> {
        let (from, to) = {
            let conclusion = self.get(conclusion);

            match conclusion {
                Term::App { decl, args, .. }
                        if (decl == "=" || decl == "~") && args.len() == 2 => {
                    (args[0].clone(), args[1].clone())
                },

                other => return Err(Error::WrongProofShape(conclusion.clone())),
            }
        };

        match self.get_mut(&to).set_reverse_monotonicity(from.clone()) {
            Err(Error::ReverseMonoNotForApp(_, _)) => (),
            other => other?
        };

        match self.get_mut(&from).set_eq_expl(EqExpl::ProofOfRewrite { id: to }) {
            Err(Error::EqExplNotForApp(_, _)) => Ok(()),
            other => other,
        }
    }

    fn proof_mono_blame(&mut self, arguments: &Vec<Id>, conclusion: &Id) -> Result<()> {
        let (from, to) = {
            let conclusion = self.get(conclusion);

            match conclusion {
                Term::App { decl, args, .. }
                if (decl == "=" || decl == "~") && args.len() == 2 => {
                    (args[0].clone(), args[1].clone())
                },

                other => return Err(Error::WrongProofShape(conclusion.clone())),
            }
        };

        match self.get_mut(&to).set_reverse_monotonicity(from.clone()) {
            Err(Error::ReverseMonoNotForApp(_, _)) => (),
            other => other?
        };

        let substitutions = {
            let conclusion = self.get(conclusion);
            let from_term = self.get(&from);
            let to_term = self.get(&to);

            match (from_term, to_term) {
                (Term::App { args: from_args, .. }, Term::App { args: to_args, .. })
                        if from_args.len() == to_args.len() => {
                    from_args.iter().zip(to_args.iter())
                        .map(|(from, to)| Substitution::Sub(from.clone(), to.clone()))
                        .collect()
                }
                _ => return Err(Error::WrongProofShape(conclusion.clone())),
            }
        };

        match self.get_mut(&from).set_eq_expl(EqExpl::ProofOfCongruence { args: substitutions, id: to }) {
            Err(Error::EqExplNotForApp(_, _)) => Ok(()),
            other => other,
        }
    }

    pub fn process(&mut self, entry: Entry) -> Result<()> {
        match entry {
            Entry::ToolVersion(_, _, _) => {},
            Entry::MkApp { id, decl, args } =>
                self.insert(id, Term::App { decl, args: self.new_ids(args)?, meta: None })?,
            Entry::MkProof { id, decl, premises, conclusion } => {
                let conclusion = self.new_id(conclusion)?;
                let premises = self.new_ids(premises)?;

                match decl.as_str() {
                    "asserted" => {
                        println!(">>blame asserted {}", self.view_id(&conclusion));
                        self.set_blame_recursive(&conclusion, Blame::Assertion)
                    },

                    // All terms gain an appropriate equality explanation for patterns explicitly,
                    // except when they don't. Some types of rewrite are not reported, but do occur
                    // in proof trees as rewrite or monotonicity steps, so we account those as
                    // an equality explanation as well.
                    "rewrite" | "rewrite*" => self.proof_rewrite_blame(&premises, &conclusion)?,
                    "monotonicity" => self.proof_mono_blame(&premises, &conclusion)?,
                    _ => {},
                }

                self.insert(id, Term::Proof { decl, premises, conclusion })?
            },
            Entry::MkLambda { id, name, decls, patterns, body } => {
                let decls = iter::repeat(Decl::None).take(decls).collect();
                let patterns = self.new_ids(patterns)?;
                let body = self.new_id(body)?;
                self.insert(id, Term::Lambda { name, decls, patterns, body })?;
            },
            Entry::MkQuant { id, name, decls, patterns, body } => {
                let decls = iter::repeat(Decl::None).take(decls).collect();
                let patterns = self.new_ids(patterns)?;
                let body = self.new_id(body)?;
                self.insert(id, Term::Quant { name, decls, patterns, body })?;
            },
            Entry::MkVar { id, offset } =>
                self.insert(id, Term::Var(offset))?,
            Entry::AttachVarNames { id, decls } => {
                let id = self.new_id(id)?;
                let term = self.get_mut(&id);
                let s_decls = decls.into_iter().map(|decl| match decl.name {
                    None => Decl::Sort(decl.sort),
                    Some(name) => Decl::Named { name, sort: decl.sort },
                }).collect();
                match term {
                    Term::Lambda { decls, .. } => *decls = s_decls,
                    Term::Quant { decls, .. } => *decls = s_decls,
                    other => return Err(Error::VarNamesNotForBinder(s_decls.clone(), other.clone())),
                }
            },
            Entry::AttachMeaning { id, meaning, .. } => {
                let term = self.get_mut(&self.new_id(id)?);
                let s_meaning = match meaning {
                    parser::Meaning::Rat(r) => Meaning::Rat(r),
                };
                term.set_meaning(s_meaning)?;
            },
            Entry::DecideAndOr(id1, id2) => {
                // println!("== Case Split ==");
                // println!("{}", self.view_id(&self.new_id(id1)?));
                // println!("{}", self.view_id(&self.new_id(id2)?));
            },
            Entry::TheoryInstanceDiscovered { ptr, axiom, bindings, blame } => {
                let inst = Instantiation {
                    body: None,
                    bindings: self.new_ids(bindings)?,
                    inst: InstantiationKind::Theory(TheoryInstantiation {
                        family: axiom,
                        blame: self.new_ids(blame)?,
                    })
                };
                self.insert_instantiation(ptr, inst)?;
            },
            Entry::MbqiInstanceDiscovered { ptr, id, bindings } => {
                let inst = Instantiation {
                    body: None,
                    bindings: self.new_ids(bindings)?,
                    inst: InstantiationKind::Model(ModelInstantiation {
                        quantifier: self.new_id(id)?,
                    })
                };
                self.insert_instantiation(ptr, inst)?;
            },
            Entry::NewMatch { ptr, id, pattern, bindings, blame } => {
                let inst = Instantiation {
                    body: None,
                    bindings: self.new_ids(bindings)?,
                    inst: InstantiationKind::Match(MatchInstantiation {
                        quantifier: self.new_id(id)?,

                        pattern: self.new_id(pattern)?,
                        blame: self.new_substitutions(blame)?,
                    })
                };
                self.insert_instantiation(ptr, inst)?;
            },
            Entry::Instance { ptr, id, generation } => {
                let mut instance = self.pending_instances.remove(&ptr).ok_or(Error::NoSuchInstance(ptr))?;

                instance.body = match id {
                    None => None,
                    Some(id) => {
                        let mut id = self.new_id(id)?;

                        match self.get(&id) {
                            Term::Proof { decl, premises, conclusion } if decl == "quant-inst" && premises.len() == 0 => {
                                match self.get(conclusion) {
                                    Term::App { decl, args, .. } if decl == "or" && args.len() == 2 => {
                                        // println!("Body: {}", self.view_id(&args[1]));
                                        id = args[1].clone();
                                    }
                                    _ => {},
                                }
                            }
                            _ => {},
                        }

                        Some(id)
                    }
                };

                let floating_enodes = std::mem::replace(&mut self.floating_enodes, Vec::new());

                for node in floating_enodes.into_iter() {
                    if instance.body.is_some() && self.term_contains_term(instance.body.as_ref().unwrap(), &node) {
                        println!("!!! floating attach-enode recovered: {}", self.view_id(&node));
                        let term = self.get_mut(&node);
                        if term.get_blame().is_none() {
                            term.set_blame(Blame::Instantiation(instance.clone()));
                        }
                    } else {
                        println!("!!! floating attach-enode NOT FOUND: {}", self.view_id(&node));
                    }
                }

                self.floating_enodes.clear();

                self.explain_inst(&instance, 0)?;

                self.current_instance.push(instance);
            },
            Entry::AttachEnode { id, generation } => {
                match self.current_instance.last() {
                    None => self.floating_enodes.push(self.new_id(id)?),
                    Some(instance) => {
                        let inst = instance.clone();
                        let id = self.new_id(id)?;

                        let concrete_id: Option<Id> = match &inst.body {
                            None => {
                                println!("!!! attach-enode without body !!!");
                                None
                            },
                            Some(body) => {
                                let mut concrete_term = Some(&id);

                                if !self.term_contains_term(body, &id) {
                                    // println!("!!! Term {} is not in quantifier body {} !!!", self.view_id(body), self.view_id(&id));
                                }

                                while concrete_term.is_some() && !self.term_contains_term(body, concrete_term.unwrap()) {
                                    // println!(">>>> {}", self.view_id(concrete_term.unwrap()));
                                    concrete_term = self.get(concrete_term.unwrap()).get_reverse_monotonicity().as_ref();
                                }

                                concrete_term.map(|id| id.clone())
                            },
                        };

                        if let Some(id) = concrete_id {
                            println!(">>blame inst {}", self.view_id(&id));
                            self.get_mut(&id).set_blame(Blame::Instantiation(inst.clone()))?;
                        }

                        println!(">>blame inst {}", self.view_id(&id));
                        self.get_mut(&id).set_blame(Blame::Instantiation(inst))?;
                    }
                }
            },
            Entry::EndOfInstance => {
                match self.current_instance.pop() {
                    None => return Err(Error::NoCurrentInstance),
                    Some(_) => {},
                }
            },
            Entry::EqExpl { id, explanation } => {
                let expl = match explanation {
                    parser::EqExpl::Root => EqExpl::Root,
                    parser::EqExpl::Literal { equality, id } =>
                        EqExpl::Literal { equality: self.new_id(equality)?, id: self.new_id(id)? },
                    parser::EqExpl::Axiom(root) =>
                        EqExpl::Axiom(self.new_id(root)?),
                    parser::EqExpl::CongruenceOrCommutativity { args, id } =>
                        EqExpl::CongruenceOrCommutativity { args: self.new_substitutions(args)?, id: self.new_id(id)? },
                    parser::EqExpl::Theory { name, id } =>
                        EqExpl::Theory { name, id: self.new_id(id)? },
                    parser::EqExpl::Unknown(root) =>
                        EqExpl::Unknown(self.new_id(root)?),
                };
                self.get_mut(&self.new_id(id)?).set_eq_expl(expl)?;
            },
            other => {
                // println!("{:?}", other);
            },
            /*
            Entry::ResolveLiteral { .. } => {},
            Entry::ResolveProcess(_) => {},
            Entry::BeginCheck(_) => {},
            Entry::Push(_) => {},
            Entry::Pop { .. } => {},
            Entry::Conflict(_) => {},
            Entry::Assign { .. } => {},
            Entry::Eof => {},
            */
        }

        Ok(())
    }
}