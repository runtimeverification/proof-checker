type Id = u8;
type IdList = Array<Id>;

#[derive(Debug, PartialEq, Drop, Clone)]
struct ImpliesType {
    left: Option<Box<Pattern>>,
    right: Option<Box<Pattern>>,
}

#[derive(Debug, PartialEq, Drop, Clone)]
struct AppType {
    left: Option<Box<Pattern>>,
    right: Option<Box<Pattern>>,
}

#[derive(Debug, PartialEq, Drop, Clone)]
struct ExistsType {
    var: Id,
    subpattern: Option<Box<Pattern>>,
}

#[derive(Debug, PartialEq, Drop, Clone)]
struct MuType {
    var: Id,
    subpattern: Option<Box<Pattern>>,
}

#[derive(Debug, PartialEq, Drop, Clone)]
struct MetaVarType {
    id: Id,
    e_fresh: IdList,
    s_fresh: IdList,
    positive: IdList,
    negative: IdList,
    app_ctx_holes: IdList,
}

#[derive(Debug, PartialEq, Drop, Clone)]
struct ESubstType {
    pattern: Option<Box<Pattern>>,
    evar_id: Id,
    plug: Option<Box<Pattern>>,
}

#[derive(Debug, PartialEq, Drop, Clone)]
struct SSubstType {
    pattern: Option<Box<Pattern>>,
    svar_id: Id,
    plug: Option<Box<Pattern>>,
}

#[derive(Debug, PartialEq, Drop, Clone)]
enum Pattern {
    EVar: Id,
    SVar: Id,
    Symbol: Id,
    Implies: ImpliesType, // left, right
    App: AppType, // left, right
    Exists: ExistsType, // var, subpattern
    Mu: MuType, // var, subpattern
    MetaVar: MetaVarType, // id, e_fresh, s_fresh, positive, negative, app_ctx_holes
    ESubst: ESubstType, // pattern, evar_id, plug
    SSubst: SSubstType // pattern, svar_id, plug
}

trait PatternTrait {
    fn e_fresh(self: @Pattern, evar: Id) -> core::bool;
    fn s_fresh(self: @Pattern, svar: Id) -> core::bool;
    fn positive(self: @Pattern, svar: Id) -> core::bool;
    fn negative(self: @Pattern, svar: Id) -> core::bool;
    fn well_formed(self: @Pattern) -> core::bool;
    fn is_redundant_subst(self: @Pattern) -> core::bool;
}

fn contains(idlist: @IdList, id: Id) -> bool {
    let mut list_span = idlist.span();

    loop {
        match list_span.pop_front() {
            Option::Some(v) => { if *v == id {
                break true;
            } },
            Option::None => { break false; },
        };
    }
}

use core::gas;

impl PatternTraitImpl of PatternTrait {
    fn e_fresh(self: @Pattern, evar: Id) -> core::bool {
        match self {
            Pattern::EVar(name) => *name != evar,
            Pattern::SVar(_) => true,
            Pattern::Symbol(_) => true,
            Pattern::Implies(ImpliesType{left, right}) => {
                let left_unbox = left.clone().unwrap().unbox();
                let right_unbox = right.clone().unwrap().unbox();
                left_unbox.e_fresh(evar) && right_unbox.e_fresh(evar)
            },
            Pattern::App(AppType{left, right}) => {
                let left_unbox = left.clone().unwrap().unbox();
                let right_unbox = right.clone().unwrap().unbox();
                left_unbox.e_fresh(evar) && right_unbox.e_fresh(evar)
            },
            Pattern::Exists(ExistsType{var, subpattern}) => {
                let supattern_unbox = subpattern.clone().unwrap().unbox();
                evar == *var || supattern_unbox.e_fresh(evar)
            },
            Pattern::Mu(MuType{subpattern, ..}) => {
                let supattern_unbox = subpattern.clone().unwrap().unbox();
                supattern_unbox.e_fresh(evar)
            },
            Pattern::MetaVar(MetaVarType{e_fresh, ..}) => { contains(e_fresh, evar) },
            Pattern::ESubst(ESubstType{pattern, evar_id, plug})  => {
                let plug_unbox = plug.clone().unwrap().unbox();
                if evar == *evar_id { return plug_unbox.e_fresh(evar);}
                let pattern_unbox = pattern.clone().unwrap().unbox();
                pattern_unbox.e_fresh(evar) && plug_unbox.e_fresh(evar)
            },
            Pattern::SSubst(SSubstType{pattern, plug, ..}) => {
                let pattern_unbox = pattern.clone().unwrap().unbox();
                let plug_unbox = plug.clone().unwrap().unbox();
                pattern_unbox.e_fresh(evar) && plug_unbox.e_fresh(evar)
            },
        }
    }

    fn s_fresh(self: @Pattern, svar: Id) -> core::bool {
        match self {
            Pattern::EVar(_) => true,
            Pattern::SVar(name) => *name != svar,
            Pattern::Symbol(_) => true,
            Pattern::Implies(ImpliesType{left, right}) => {
                let left_unbox = left.clone().unwrap().unbox();
                let right_unbox = right.clone().unwrap().unbox();
                left_unbox.s_fresh(svar) && right_unbox.s_fresh(svar)
            },
            Pattern::App(AppType{left, right}) => {
                let left_unbox = left.clone().unwrap().unbox();
                let right_unbox = right.clone().unwrap().unbox();
                left_unbox.s_fresh(svar) && right_unbox.s_fresh(svar)
            },
            Pattern::Exists(ExistsType{subpattern, ..}) => {
                let supattern_unbox = subpattern.clone().unwrap().unbox();
                supattern_unbox.s_fresh(svar)
            },
            Pattern::Mu(MuType{var, subpattern}) => {
                let supattern_unbox = subpattern.clone().unwrap().unbox();
                svar == *var || supattern_unbox.s_fresh(svar)
            },
            Pattern::MetaVar(MetaVarType{s_fresh, ..}) => { contains(s_fresh, svar) },
            Pattern::ESubst(ESubstType{pattern, plug, ..}) => {
                let pattern_unbox = pattern.clone().unwrap().unbox();
                let plug_unbox = plug.clone().unwrap().unbox();
                pattern_unbox.s_fresh(svar) && plug_unbox.s_fresh(svar)
            },
            Pattern::SSubst(SSubstType{pattern, svar_id, plug}) => {
                let plug_unbox = plug.clone().unwrap().unbox();
                if svar == *svar_id { return plug_unbox.s_fresh(svar); }
                let pattern_unbox = pattern.clone().unwrap().unbox();
                pattern_unbox.s_fresh(svar) && plug_unbox.s_fresh(svar)
            },
        }
    }

    fn positive(self: @Pattern, svar: Id) -> core::bool {
        gas::withdraw_gas().unwrap();
        match self {
            Pattern::EVar(_) => true,
            Pattern::SVar(_) => true,
            Pattern::Symbol(_) => true,
            Pattern::Implies(ImpliesType{left, right}) => {
                let left_unbox = left.clone().unwrap().unbox();
                let right_unbox = right.clone().unwrap().unbox();
                left_unbox.negative(svar) &&  right_unbox.positive(svar)
            },
            Pattern::App(AppType{left, right}) => {
                let left_unbox = left.clone().unwrap().unbox();
                let right_unbox = right.clone().unwrap().unbox();
                left_unbox.positive(svar) && right_unbox.positive(svar)
            },
            Pattern::Exists(ExistsType{subpattern, ..}) => {
                let supattern_unbox = subpattern.clone().unwrap().unbox();
                supattern_unbox.positive(svar)
            },
            Pattern::Mu(MuType{var, subpattern}) => {
                let supattern_unbox = subpattern.clone().unwrap().unbox();
                svar == *var ||  supattern_unbox.positive(svar)
            },
            Pattern::MetaVar(MetaVarType{positive, ..}) => { contains(positive, svar) },
            Pattern::ESubst(ESubstType{pattern, plug, ..}) => {
                let pattern_unbox = pattern.clone().unwrap().unbox();
                let plug_unbox = plug.clone().unwrap().unbox();
                pattern_unbox.positive(svar) && plug_unbox.s_fresh(svar)
            },
            Pattern::SSubst(SSubstType{pattern, svar_id, plug}) => {
                let pattern_unbox = pattern.clone().unwrap().unbox();
                let plug_unbox = plug.clone().unwrap().unbox();
                let plug_positive_svar = plug_unbox.s_fresh(svar)
                    || (pattern_unbox.positive(*svar_id) && plug_unbox.positive(svar))
                    || (pattern_unbox.negative(*svar_id) && plug_unbox.negative(svar));

                    if svar == *svar_id { return plug_positive_svar; }

                    return pattern_unbox.positive(svar) && plug_positive_svar;
            },
        }
    }

    fn negative(self: @Pattern, svar: Id) -> core::bool {
        gas::withdraw_gas().unwrap();
        match self {
            Pattern::EVar(_) => true,
            Pattern::SVar(name) => *name != svar,
            Pattern::Symbol(_) => true,
            Pattern::Implies(ImpliesType{left, right}) => {
                let left_unbox = left.clone().unwrap().unbox();
                let right_unbox = right.clone().unwrap().unbox();
                left_unbox.positive(svar) && right_unbox.negative(svar)
            },
            Pattern::App(AppType{left, right}) => {
                let left_unbox = left.clone().unwrap().unbox();
                let right_unbox = right.clone().unwrap().unbox();
                left_unbox.negative(svar) && right_unbox.negative(svar)
            },
            Pattern::Exists(ExistsType{subpattern, ..}) => {
                let supattern_unbox = subpattern.clone().unwrap().unbox();
                supattern_unbox.negative(svar)
            },
            Pattern::Mu(MuType{var, subpattern}) => {
                let supattern_unbox = subpattern.clone().unwrap().unbox();
                svar == *var || supattern_unbox.negative(svar)
            },
            Pattern::MetaVar(MetaVarType{negative, ..}) => { contains(negative, svar) },
            Pattern::ESubst(ESubstType{pattern, plug, ..}) => {
                let pattern_unbox = pattern.clone().unwrap().unbox();
                let plug_unbox = plug.clone().unwrap().unbox();
                pattern_unbox.negative(svar) && plug_unbox.s_fresh(svar)
            },
            Pattern::SSubst(SSubstType{pattern, svar_id, plug}) => {
                let pattern_unbox = pattern.clone().unwrap().unbox();
                let plug_unbox = plug.clone().unwrap().unbox();
                let plug_negative_svar = plug_unbox.s_fresh(svar)
                    || (pattern_unbox.positive(*svar_id) && plug_unbox.negative(svar))
                    || (pattern_unbox.negative(*svar_id) && plug_unbox.positive(svar));

                if svar == *svar_id { return plug_negative_svar; }

                return  pattern_unbox.negative(svar) && plug_negative_svar;
            },
        }
    }

    fn well_formed(self: @Pattern) -> core::bool {
        true
    }

    fn is_redundant_subst(self: @Pattern) -> core::bool {
        true
    }
}

/// Pattern construction utilities
/// ------------------------------
fn evar(id: Id) -> Pattern {
    return Pattern::EVar(id);
}

fn svar(id: Id) -> Pattern {
    return Pattern::SVar(id);
}

fn symbol(id: Id) -> Pattern {
    return Pattern::Symbol(id);
}

fn implies(left: Pattern, right: Pattern) -> Pattern {
    let left = Option::Some(BoxTrait::new(left));
    let right = Option::Some(BoxTrait::new(right));
    return Pattern::Implies(ImpliesType { left: left, right: right });
}

fn app(left: Pattern, right: Pattern) -> Pattern {
    let left = Option::Some(BoxTrait::new(left));
    let right = Option::Some(BoxTrait::new(right));
    return Pattern::App(AppType { left: left, right: right });
}

fn exists(var: Id, subpattern: Pattern) -> Pattern {
    let subpattern = Option::Some(BoxTrait::new(subpattern));
    return Pattern::Exists(ExistsType { var: var, subpattern: subpattern });
}

fn mu(var: Id, subpattern: Pattern) -> Pattern {
    let subpattern = Option::Some(BoxTrait::new(subpattern));
    return Pattern::Mu(MuType { var: var, subpattern: subpattern });
}

fn metavar(
    id: Id,
    e_fresh: IdList,
    s_fresh: IdList,
    positive: IdList,
    negative: IdList,
    app_ctx_holes: IdList
) -> Pattern {
    return Pattern::MetaVar(
        MetaVarType {
            id: id,
            e_fresh: e_fresh,
            s_fresh: s_fresh,
            positive: positive,
            negative: negative,
            app_ctx_holes: app_ctx_holes
        }
    );
}

fn metavar_unconstrained(id: Id) -> Pattern {
    let e_fresh: IdList = array![];
    let s_fresh: IdList = array![];
    let positive: IdList = array![];
    let negative: IdList = array![];
    let app_ctx_holes: IdList = array![];
    return Pattern::MetaVar(
        MetaVarType {
            id: id,
            e_fresh: e_fresh,
            s_fresh: s_fresh,
            positive: positive,
            negative: negative,
            app_ctx_holes: app_ctx_holes
        }
    );
}

fn metavar_s_fresh(var_id: Id, fresh: Id, positive: IdList, negative: IdList) -> Pattern {
    let e_fresh: IdList = array![];
    let s_fresh: IdList = array![fresh];
    let app_ctx_holes: IdList = array![];
    return Pattern::MetaVar(
        MetaVarType {
            id: var_id,
            e_fresh: e_fresh,
            s_fresh: s_fresh,
            positive: positive,
            negative: negative,
            app_ctx_holes: app_ctx_holes
        }
    );
}

fn metavar_e_fresh(var_id: Id, fresh: Id, positive: IdList, negative: IdList) -> Pattern {
    let e_fresh: IdList = array![fresh];
    let s_fresh: IdList = array![];
    let app_ctx_holes: IdList = array![];
    return Pattern::MetaVar(
        MetaVarType {
            id: var_id,
            e_fresh: e_fresh,
            s_fresh: s_fresh,
            positive: positive,
            negative: negative,
            app_ctx_holes: app_ctx_holes
        }
    );
}

fn esubst(pattern: Pattern, evar_id: Id, plug: Pattern) -> Pattern {
    let pattern = Option::Some(BoxTrait::new(pattern));
    let plug = Option::Some(BoxTrait::new(plug));
    return Pattern::ESubst(ESubstType { pattern: pattern, evar_id: evar_id, plug: plug });
}

fn ssubst(pattern: Pattern, svar_id: Id, plug: Pattern) -> Pattern {
    let pattern = Option::Some(BoxTrait::new(pattern));
    let plug = Option::Some(BoxTrait::new(plug));
    return Pattern::SSubst(SSubstType { pattern: pattern, svar_id: svar_id, plug: plug });
}

// Notation
#[inline(always)]
fn bot() -> Pattern {
    return mu(0, svar(0));
}

#[inline(always)]
fn not(pat: Pattern) -> Pattern {
    return implies(pat, bot());
}

fn forall(evar: Id, pat: Pattern) -> Pattern {
    return not(exists(evar, not(pat)));
}

impl PatternOptionBoxPartialEq of PartialEq<Option<Box<Pattern>>> {
    fn eq(lhs: @Option<Box<Pattern>>, rhs: @Option<Box<Pattern>>) -> core::bool {
        match lhs {
            Option::Some(lhs) => {
                match (rhs) {
                    Option::Some(rhs) => { lhs.as_snapshot().unbox() == rhs.as_snapshot().unbox() },
                    Option::None => { false }
                }
            },
            Option::None => {
                match (rhs) {
                    Option::Some(_) => { false },
                    Option::None => { true }
                }
            }
        }
    }


    fn ne(lhs: @Option<Box<Pattern>>, rhs: @Option<Box<Pattern>>) -> core::bool {
        !(lhs == rhs)
    }
}

impl PatternOptionBoxClone of Clone<Option<Box<Pattern>>> {
    fn clone(self: @Option<Box<Pattern>>) -> Option<Box<Pattern>> {
        match self {
            Option::Some(box_pat) => {
                let mut result: Pattern = box_pat.as_snapshot().unbox().clone();
                return Option::Some(BoxTrait::new(result));
            },
            Option::None => { Option::None }
        }
    }
}

#[cfg(test)]
mod tests {
    use core::array::ArrayTrait;

    use super::evar;
    use super::exists;
    use super::implies;
    use super::metavar_s_fresh;
    use super::app;
    use super::esubst;
    use super::ssubst;
    use super::PatternTrait;

    #[test]
    #[available_gas(1000000000000000)]
    fn test_efresh() {
        let evar = evar(1);
        let left = exists(1, evar.clone());
        assert!(left.e_fresh(1));

        let right = exists(2, evar);
        assert!(!right.e_fresh(1));

        let implication = implies(left.clone(), right.clone());
        assert!(!implication.e_fresh(1));

        let mut positive = ArrayTrait::<u8>::new();
        positive.append(2);
        let mut negative = ArrayTrait::<u8>::new();
        negative.append(2);
        let mvar = metavar_s_fresh(1, 2, positive, negative);
        let metaapp = app(left.clone(), mvar);
        assert!(!metaapp.e_fresh(2));

        let esubst_ = esubst(right.clone(), 1, left.clone());
        assert!(esubst_.e_fresh(1));

        let ssubst_ = ssubst(right, 1, left);
        assert!(!ssubst_.e_fresh(1));
    }

    use super::svar;
    use super::mu;
    #[test]
    #[available_gas(1000000000000000)]
    fn test_sfresh() {
        let svar = svar(1);
        let left = mu(1, svar.clone());
        assert!(left.s_fresh(1));

        let right = mu(2, svar);
        assert!(!right.s_fresh(1));

        let implication = implies(left.clone(), right.clone());
        assert!(!implication.s_fresh(1));

        let mut positive = ArrayTrait::<u8>::new();
        positive.append(2);
        let mut negative = ArrayTrait::<u8>::new();
        negative.append(2);
        let mvar = metavar_s_fresh(1, 2, positive, negative);
        let metaapp = app(left.clone(), right.clone());
        assert!(!metaapp.s_fresh(1));

        let metaapp2 = app(left.clone(), mvar);
        assert!(metaapp2.s_fresh(2));

        let esubst_ = esubst(right.clone(), 1, left.clone());
        assert!(!esubst_.s_fresh(1));

        let ssubst_ = ssubst(right, 1, left);
        assert!(ssubst_.s_fresh(1));
    }

    use super::symbol;
    use super::metavar_unconstrained;
    use super::not;
    #[test]
    #[available_gas(1000000000000000)]
    fn test_positivity() {
        let x0 = svar(0);
        let x1 = svar(1);
        let x2 = svar(2);
        let c1 = symbol(1);
        let neg_x1 = not(x1.clone());

        // EVar
        let evar1 = evar(1);
        assert!(evar1.positive(1));
        assert!(evar1.negative(1));
        assert!(evar1.positive(2));
        assert!(evar1.negative(2));

        // SVar
        assert!(x1.positive(1));
        assert!(!x1.negative(1));
        assert!(x1.positive(2));
        assert!(x1.negative(2));

        // Symbol
        assert!(c1.positive(1));
        assert!(c1.negative(1));
        assert!(c1.positive(2));
        assert!(c1.negative(2));

        // App
        let appx1x2 = app(x1.clone(), x2.clone());
        assert!(appx1x2.positive(1));
        assert!(appx1x2.positive(2));
        assert!(appx1x2.positive(3));
        assert!(!appx1x2.negative(1));
        assert!(!appx1x2.negative(2));
        assert!(appx1x2.negative(3));

        // Implies
        let impliesx1x2 = implies(x1.clone(), x2.clone());
        assert!(!impliesx1x2.positive(1));
        assert!(impliesx1x2.positive(2));
        assert!(impliesx1x2.positive(3));
        assert!(impliesx1x2.negative(1));
        assert!(!impliesx1x2.negative(2));
        assert!(impliesx1x2.negative(3));

        let impliesx1x1 = implies(x1.clone(), x1.clone());
        assert!(!impliesx1x1.positive(1));
        assert!(!impliesx1x1.negative(1));

        // Exists
        let existsx1x2 = exists(1, x2.clone());
        assert!(existsx1x2.positive(1));
        assert!(existsx1x2.positive(2));
        assert!(existsx1x2.positive(3));
        assert!(existsx1x2.negative(1));
        assert!(!existsx1x2.negative(2));
        assert!(existsx1x2.negative(3));

        let existsx1nx2 = exists(1, not(x2.clone()));
        assert!(existsx1nx2.negative(2));

        // Mu
        let mux1evar1 = mu(1, evar1.clone());
        assert!(mux1evar1.positive(1));
        assert!(mux1evar1.positive(2));
        assert!(mux1evar1.negative(1));
        assert!(mux1evar1.negative(2));

        let mux1x1 = mu(1, x1.clone());
        assert!(mux1x1.positive(1));
        assert!(mux1x1.negative(1));

        let mux1x2 = mu(1, x2.clone());
        assert!(mux1x2.positive(1));
        assert!(mux1x2.positive(2));
        assert!(mux1x2.positive(3));
        assert!(mux1x2.negative(1));
        assert!(!mux1x2.negative(2));
        assert!(mu(1, implies(x2.clone(), x1.clone())).negative(2));
        assert!(mux1x2.negative(3));

        // MetaVar
        assert!(!metavar_unconstrained(1).positive(1));
        assert!(!metavar_unconstrained(1).positive(2));
        assert!(!metavar_unconstrained(1).negative(1));
        assert!(!metavar_unconstrained(1).negative(2));

        // Do not imply positivity from freshness
        assert!(!metavar_s_fresh(1, 1, ArrayTrait::<u8>::new(), ArrayTrait::<u8>::new()).positive(1));
        assert!(!metavar_s_fresh(1, 1, ArrayTrait::<u8>::new(), ArrayTrait::<u8>::new()).negative(1));
        let mut positive1 = ArrayTrait::<u8>::new();
        positive1.append(1);
        let mut negative1 = ArrayTrait::<u8>::new();
        negative1.append(1);
        assert!(metavar_s_fresh(1, 1, positive1.clone(), negative1.clone()).positive(1));
        assert!(metavar_s_fresh(1, 1, positive1.clone(), negative1.clone()).negative(1));
        assert!(metavar_s_fresh(1, 1, positive1.clone(), ArrayTrait::<u8>::new()).positive(1));
        assert!(metavar_s_fresh(1, 1, ArrayTrait::<u8>::new(), negative1).negative(1));

        assert!(!metavar_s_fresh(1, 1, ArrayTrait::<u8>::new(), ArrayTrait::<u8>::new()).positive(2));
        assert!(!metavar_s_fresh(1, 1, ArrayTrait::<u8>::new(), ArrayTrait::<u8>::new()).negative(2));

        // ESubst
        assert!(!esubst(metavar_unconstrained(0), 0, x0.clone()).positive(0));
        assert!(!esubst(metavar_unconstrained(0), 0, x1.clone()).positive(0));
        assert!(!esubst(metavar_s_fresh(0, 1, positive1.clone(), ArrayTrait::<u8>::new()), 0, x1.clone()).positive(0));

        assert!(!esubst(metavar_unconstrained(0), 0, x0.clone()).negative(0));
        assert!(!esubst(metavar_unconstrained(0), 0, x1.clone()).negative(0));
        assert!(!esubst(metavar_s_fresh(0, 1, positive1.clone(), ArrayTrait::<u8>::new()), 0, x1.clone()).negative(0));

        // SSubst
        assert!(!ssubst(metavar_unconstrained(0), 0, x0.clone()).positive(0));
        assert!(ssubst(metavar_unconstrained(0), 0, x1.clone()).positive(0));
        assert!(ssubst(metavar_s_fresh(0, 1, positive1.clone(), ArrayTrait::<u8>::new()), 0, x1.clone()).positive(0));

        assert!(!ssubst(metavar_unconstrained(0), 0, x0.clone()).negative(0));
        assert!(ssubst(metavar_unconstrained(0), 0, x1.clone()).negative(0));
        assert!(ssubst(metavar_s_fresh(0, 1, positive1, ArrayTrait::<u8>::new()), 0, x1.clone()).negative(0));

        // Combinations
        assert!(!neg_x1.positive(1));
        assert!(neg_x1.positive(2));
        assert!(neg_x1.negative(1));
        assert!(neg_x1.negative(2));

        let negx1_implies_negx1 = implies(neg_x1.clone(), neg_x1.clone());
        assert!(!negx1_implies_negx1.positive(1));
        assert!(negx1_implies_negx1.positive(2));
        assert!(!negx1_implies_negx1.negative(1));
        assert!(negx1_implies_negx1.negative(2));

        let negx1_implies_x1 = implies( neg_x1.clone(), x1.clone());
        assert!(negx1_implies_x1.positive(1));
        assert!(!negx1_implies_x1.negative(1));
    }
}
