use bumpalo::Bump;
use std::{cell::Cell, collections::HashMap};
use thiserror::Error;

#[derive(Copy, Clone, Debug)]
pub enum Expr<'hm> {
    Unit,
    Identifier(&'hm str),
    Lambda(&'hm str, &'hm Self),
    Appl(&'hm Self, &'hm Self),
    Let(&'hm str, &'hm Self, &'hm Self),
}

#[derive(Debug, Error)]
#[error("type error")]
pub struct TypeError;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Ty<'hm> {
    TUnit,
    TVar(&'hm Cell<Typevar<'hm>>),
    Fn(&'hm Self, &'hm Self),
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Typevar<'hm> {
    Bound(Ty<'hm>),
    Unbound(TypevarId, Level),
}

#[derive(Clone)]
pub struct Polytype<'hm>(Vec<TypevarId>, Ty<'hm>);

type TypevarId = u32;

type Level = u32;

pub struct AlgorithmJ<'hm> {
    current_level: Level,
    current_typevar: TypevarId,
    bump: &'hm Bump,
}

impl<'hm> AlgorithmJ<'hm> {
    pub fn new(bump: &'hm Bump) -> Self {
        AlgorithmJ {
            current_level: 0,
            current_typevar: 0,
            bump,
        }
    }

    fn enter_level(&mut self) {
        self.current_level += 1;
    }

    fn exit_level(&mut self) {
        self.current_level -= 1;
    }

    fn newvar(&mut self) -> TypevarId {
        self.current_typevar += 1;
        self.current_typevar
    }

    fn newvar_t(&mut self) -> Ty<'hm> {
        Ty::TVar(self.bump.alloc(Cell::new(Typevar::Unbound(
            self.newvar(),
            self.current_level,
        ))))
    }

    /// Instantiate a concrete type from a polytype
    fn inst(&mut self, Polytype(typevars, ty): &Polytype<'hm>) -> Ty<'hm> {
        fn replace_typevars<'hm>(
            bump: &'hm Bump,
            tbl: &HashMap<TypevarId, Ty<'hm>>,
            ty: &Ty<'hm>,
        ) -> Ty<'hm> {
            match ty {
                Ty::TUnit => Ty::TUnit,
                Ty::TVar(tvar) => match tvar.get() {
                    Typevar::Bound(t) => replace_typevars(bump, tbl, &t),
                    Typevar::Unbound(n, _level) => match tbl.get(&n) {
                        Some(t_prime) => *t_prime,
                        None => *ty,
                    },
                },
                Ty::Fn(a, b) => Ty::Fn(
                    bump.alloc(replace_typevars(bump, tbl, a)),
                    bump.alloc(replace_typevars(bump, tbl, b)),
                ),
            }
        }
        let typevars_to_replace = typevars
            .iter()
            .map(|tvar| (*tvar, self.newvar_t()))
            .collect();
        replace_typevars(self.bump, &typevars_to_replace, &ty)
    }

    fn generalize(&self, t: Ty<'hm>) -> Polytype<'hm> {
        let mut typevars = vec![];
        self.find_all_typevars(t, &mut typevars);
        typevars.sort_unstable();
        typevars.dedup();
        Polytype(typevars, t)
    }

    /// Helper for [`AlgorithmJ::generalize`]
    fn find_all_typevars(&self, ty: Ty<'hm>, tvs: &mut Vec<TypevarId>) {
        match ty {
            Ty::TUnit => {}
            Ty::TVar(tvar) => match tvar.get() {
                Typevar::Bound(t) => self.find_all_typevars(t, tvs),
                Typevar::Unbound(n, level) => {
                    if self.current_level < level {
                        tvs.push(n);
                    }
                }
            },
            Ty::Fn(a, b) => {
                self.find_all_typevars(*a, tvs);
                self.find_all_typevars(*b, tvs);
            }
        }
    }

    pub fn infer(
        &mut self,
        env: &HashMap<&'hm str, Polytype<'hm>>,
        expr: &Expr<'hm>,
    ) -> Result<Ty<'hm>, TypeError> {
        match expr {
            Expr::Unit => Ok(Ty::TUnit),
            Expr::Identifier(ident) => {
                let poly = env.get(*ident).ok_or(TypeError)?;
                let inst = self.inst(poly);
                Ok(inst)
            }
            Expr::Lambda(input, body) => {
                let input_type = self.newvar_t();
                let mut lambda_env = env.clone();
                lambda_env.insert(input, Polytype(vec![], input_type));
                let body_type = self.infer(&lambda_env, body)?;
                Ok(Ty::Fn(
                    self.bump.alloc(input_type),
                    self.bump.alloc(body_type),
                ))
            }
            Expr::Appl(function, arg) => {
                let function_type = self.infer(env, function)?;
                let arg_type = self.infer(env, arg)?;
                let return_type = self.newvar_t();
                unify(
                    function_type,
                    Ty::Fn(self.bump.alloc(arg_type), self.bump.alloc(return_type)),
                )?;
                Ok(return_type)
            }
            Expr::Let(var, value, body) => {
                self.enter_level();
                let value_type = self.infer(env, value)?;
                self.exit_level();
                let mut let_env = env.clone();
                let_env.insert(var, self.generalize(value_type));
                let body_type = self.infer(&let_env, body)?;
                Ok(body_type)
            }
        }
    }
}

fn occurs(a_id: TypevarId, a_level: Level, ty: Ty<'_>) -> bool {
    match ty {
        Ty::TUnit => false,
        Ty::TVar(tvar) => match tvar.get() {
            Typevar::Bound(t) => occurs(a_id, a_level, t),
            Typevar::Unbound(b_id, b_level) => {
                let min_level = a_level.min(b_level);
                tvar.set(Typevar::Unbound(b_id, min_level));
                a_id == b_id
            }
        },
        Ty::Fn(b, c) => occurs(a_id, a_level, *b) || occurs(a_id, a_level, *c),
    }
}

fn unify<'bump>(ty1: Ty<'bump>, ty2: Ty<'bump>) -> Result<(), TypeError> {
    match (ty1, ty2) {
        (Ty::TUnit, Ty::TUnit) => Ok(()),
        (Ty::TVar(a), b) | (b, Ty::TVar(a)) => match a.get() {
            Typevar::Bound(a_prime) => unify(a_prime, b),
            Typevar::Unbound(a_id, a_level) => {
                if ty1 != ty2 {
                    if occurs(a_id, a_level, b) {
                        return Err(TypeError);
                    }
                    a.set(Typevar::Bound(b));
                }
                Ok(())
            }
        },
        (Ty::Fn(a, b), Ty::Fn(c, d)) => {
            unify(*a, *c)?;
            unify(*b, *d)
        }
        _ => Err(TypeError),
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::{self, Write};

    struct Pp {
        buf: String,
        ch: u8,
        map: HashMap<TypevarId, char>,
    }

    impl Pp {
        fn pp_ty(&mut self, ty: Ty<'_>) -> fmt::Result {
            match ty {
                Ty::TUnit => write!(&mut self.buf, "unit"),
                Ty::TVar(tvar) => self.pp_tvar(tvar.get()),
                Ty::Fn(a, b) => {
                    if Self::should_parenthesize(*a) {
                        write!(&mut self.buf, "(")?;
                        self.pp_ty(*a)?;
                        write!(&mut self.buf, ")")?;
                    } else {
                        self.pp_ty(*a)?;
                    }
                    write!(&mut self.buf, " -> ")?;
                    self.pp_ty(*b)
                }
            }
        }

        fn pp_tvar(&mut self, tvar: Typevar<'_>) -> fmt::Result {
            match tvar {
                Typevar::Bound(ty) => self.pp_ty(ty),
                Typevar::Unbound(typevar, _) => {
                    let letter = self.get_letter(typevar);
                    write!(&mut self.buf, "{}", letter)
                }
            }
        }

        fn get_letter(&mut self, id: TypevarId) -> char {
            *self.map.entry(id).or_insert_with(|| {
                let ch = self.ch as char;
                self.ch += 1;
                ch
            })
        }

        /// If this type is the a in a -> b, should it be parenthesized?
        fn should_parenthesize(ty: Ty<'_>) -> bool {
            match ty {
                Ty::TVar(tvar) => match tvar.get() {
                    Typevar::Bound(t_prime) => Self::should_parenthesize(t_prime),
                    _ => false,
                },
                Ty::Fn(_, _) => true,
                _ => false,
            }
        }
    }

    fn pp(ty: Ty<'_>) -> String {
        let mut pp = Pp {
            buf: String::with_capacity(32),
            ch: b'a',
            map: HashMap::new(),
        };
        pp.pp_ty(ty).unwrap();
        pp.buf
    }

    use super::*;

    peg::parser! {
      grammar parse<'hm>(bump: &'hm Bump) for str {
        rule ident() -> &'hm str = ident:$(['a'..='z']+) {
            bump.alloc_str(ident)
        }

        rule _ = [' '|'\n']*

        pub rule expr() -> &'hm Expr<'hm> = precedence! {
            ident:ident() {
                bump.alloc(Expr::Identifier(ident))
            }
            "\\" _ arg:ident() _ "." _ body:expr() {
                bump.alloc(Expr::Lambda(arg, body))
            }
            function:(@) _ body:@ {
                bump.alloc(Expr::Appl(function, body))
            }
            // Parsing let expressions doesn't work for some reason
            // "let" _ var:ident() _ "=" _ value:expr() _ "in" _ body:expr() {
            //     bump.alloc(Expr::Let(var, value, body))
            // }
            --
            "(" expr:expr() ")" {
                expr
            }
        }
      }
    }

    fn check(expr: &str, ty: &str) {
        let bump = Bump::new();
        let mut j = AlgorithmJ::new(&bump);
        let env = HashMap::new();

        let e = parse::expr(expr, &bump).expect("expr parsing failed");

        let t = j.infer(&env, &e).expect("inference failed");
        assert_eq!(ty, pp(t));
    }

    #[test]
    fn infer_1() {
        check(r"\f.\x. f x", "(a -> b) -> a -> b");
    }

    #[test]
    fn infer_2() {
        check(r"\f.\x. f (f x)", "(a -> a) -> a -> a");
    }

    #[test]
    fn infer_3() {
        check(
            r"\m.\n.\f.\x. m f (n f x)",
            "(a -> b -> c) -> (a -> d -> b) -> a -> d -> c",
        );
    }

    #[test]
    fn infer_succ() {
        check(
            r"\n.\f.\x. f (n f x)",
            "((a -> b) -> c -> a) -> (a -> b) -> c -> b",
        );
    }

    #[test]
    fn infer_mult() {
        check(
            r"\m.\n.\f.\x. m (n f) x",
            "(a -> b -> c) -> (d -> a) -> d -> b -> c",
        );
    }

    #[test]
    fn infer_pred() {
        check(
            r"\n.\f.\x. n (\g.\h. h (g f)) (\u.x) (\u.u)",
            "(((a -> b) -> (b -> c) -> c) -> (d -> e) -> (f -> f) -> g) -> a -> e -> g",
        );
    }

    #[test]
    fn infer_let1() {
        // \x. let y = x in y : a -> a
        let bump = Bump::new();
        let mut j = AlgorithmJ::new(&bump);
        let env = HashMap::new();

        let e = Expr::Lambda(
            "x",
            &Expr::Let("y", &Expr::Identifier("x"), &Expr::Identifier("y")),
        );
        let t = j.infer(&env, &e).unwrap();
        assert_eq!("a -> a", pp(t));
    }

    #[test]
    fn infer_let2() {
        // \x. let y = \z.x in y : 'a -> 'b -> 'a
        let bump = Bump::new();
        let mut j = AlgorithmJ::new(&bump);
        let env = HashMap::new();

        let e = Expr::Lambda(
            "x",
            &Expr::Let(
                "y",
                &Expr::Lambda("z", &Expr::Identifier("x")),
                &Expr::Identifier("y"),
            ),
        );
        let t = j.infer(&env, &e).unwrap();
        assert_eq!("a -> b -> a", pp(t));
    }
}
