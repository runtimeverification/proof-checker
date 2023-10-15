#include "../include/data_structures.hpp"
#include <cassert>
#include <cstring>
#include <iostream>
#include <memory>

enum class Instruction {
  // Patterns
  EVar = 2,
  SVar,
  Symbol,
  Implication,
  Application,
  Mu,
  Exists,
  // Meta Patterns,
  MetaVar,
  ESubst,
  SSubst,
  // Axiom Schemas,
  Prop1,
  Prop2,
  Prop3,
  Quantifier,
  PropagationOr,
  PropagationExists,
  PreFixpoint,
  Existence,
  Singleton,
  // Inference rules,
  ModusPonens,
  Generalization,
  Frame,
  Substitution,
  KnasterTarski,
  // Meta Incference rules,
  Instantiate,
  // Stack Manipulation,
  Pop,
  // Memory Manipulation,
  Save,
  Load,
  // Journal Manipulation,
  Publish,
  // Metavar with no constraints
  CleanMetaVar = (9 + 128)

};

Instruction from(int value) {
  switch (value) {
  case 2:
    return Instruction::EVar;
  case 3:
    return Instruction::SVar;
  case 4:
    return Instruction::Symbol;
  case 5:
    return Instruction::Implication;
  case 6:
    return Instruction::Application;
  case 7:
    return Instruction::Mu;
  case 8:
    return Instruction::Exists;
  case 9:
    return Instruction::MetaVar;
  case 10:
    return Instruction::ESubst;
  case 11:
    return Instruction::SSubst;
  case 12:
    return Instruction::Prop1;
  case 13:
    return Instruction::Prop2;
  case 14:
    return Instruction::Prop3;
  case 15:
    return Instruction::Quantifier;
  case 16:
    return Instruction::PropagationOr;
  case 17:
    return Instruction::PropagationExists;
  case 18:
    return Instruction::PreFixpoint;
  case 19:
    return Instruction::Existence;
  case 20:
    return Instruction::Singleton;
  case 21:
    return Instruction::ModusPonens;
  case 22:
    return Instruction::Generalization;
  case 23:
    return Instruction::Frame;
  case 24:
    return Instruction::Substitution;
  case 25:
    return Instruction::KnasterTarski;
  case 26:
    return Instruction::Instantiate;
  case 27:
    return Instruction::Pop;
  case 28:
    return Instruction::Save;
  case 29:
    return Instruction::Load;
  case 30:
    return Instruction::Publish;
  case 137:
    return Instruction::CleanMetaVar;
  default:
    exit(1); // Bad instruction!
    break;
  }
}

using Id = int8_t;
using IdList = LinkedList<Id>;

struct Pattern {
  Instruction inst;    // All
  Id id;               // EVar, SVar, Symbol, Mu, Exists, MetaVar,
                       // ESubst (evar_id), SSubst (svar_id)
  Pattern *left;       // Implication, Application
  Pattern *right;      // Implication, Application
  Pattern *subpattern; // Exists, Mu, ESubst (pattern), SSubst (pattern)
  Pattern *plug;       // ESubst, SSubst

  IdList *e_fresh;       // MetaVar
  IdList *s_fresh;       // MetaVar
  IdList *positive;      // MetaVar
  IdList *negative;      // MetaVar
  IdList *app_ctx_holes; // MetaVar

  // Constructor for creating instances of Pattern
  static Pattern *newPattern(Instruction inst, Id id) {
    auto pattern = static_cast<Pattern *>(malloc(sizeof(Pattern)));

    pattern->id = id;
    pattern->inst = inst;
    pattern->left = nullptr;
    pattern->right = nullptr;
    pattern->subpattern = nullptr;
    pattern->plug = nullptr;

    pattern->e_fresh = nullptr;
    pattern->s_fresh = nullptr;
    pattern->positive = nullptr;
    pattern->negative = nullptr;
    pattern->app_ctx_holes = nullptr;
    return pattern;
  }

  // Copy constructor
  static Pattern *copy(Pattern *pattern) {
    auto copy = newPattern(pattern->inst, pattern->id);
    if (pattern->left) {
      copy->left = Pattern::copy(pattern->left);
    }
    if (pattern->right) {
      copy->right = Pattern::copy(pattern->right);
    }
    if (pattern->subpattern) {
      copy->subpattern = Pattern::copy(pattern->subpattern);
    }
    if (pattern->plug) {
      copy->plug = Pattern::copy(pattern->plug);
    }

    if (pattern->e_fresh) {
      copy->e_fresh = IdList::create();
      for (auto it = pattern->e_fresh->head; it; it = it->next) {
        copy->e_fresh->insert_front(it->data);
      }
    }
    if (pattern->s_fresh) {
      copy->s_fresh = IdList::create();
      for (auto it = pattern->s_fresh->head; it; it = it->next) {
        copy->s_fresh->insert_front(it->data);
      }
    }
    if (pattern->positive) {
      copy->positive = IdList::create();
      for (auto it = pattern->positive->head; it; it = it->next) {
        copy->positive->insert_front(it->data);
      }
    }
    if (pattern->negative) {
      copy->negative = IdList::create();
      for (auto it = pattern->negative->head; it; it = it->next) {
        copy->negative->insert_front(it->data);
      }
    }
    if (pattern->app_ctx_holes) {
      copy->app_ctx_holes = IdList::create();
      for (auto it = pattern->app_ctx_holes->head; it; it = it->next) {
        copy->app_ctx_holes->insert_front(it->data);
      }
    }
    return copy;
  }

  bool pattern_e_fresh(Id evar) {
    switch (inst) {
    case Instruction::EVar:
      return evar != id;
      break;
    case Instruction::SVar:
      return true;
      break;
    case Instruction::Symbol:
      return true;
      break;
    case Instruction::MetaVar:
      return e_fresh->contains(evar);
      break;
    case Instruction::Implication:
      return left->pattern_e_fresh(evar) && right->pattern_e_fresh(evar);
      break;
    case Instruction::Application:
      return left->pattern_e_fresh(evar) && right->pattern_e_fresh(evar);
      break;
    case Instruction::Exists:
      return (evar == id) || subpattern->pattern_e_fresh(evar);
      break;
    case Instruction::Mu:
      return subpattern->pattern_e_fresh(evar);
      break;
    case Instruction::ESubst:
      // Assume: substitution is well-formed => plug occurs in the result

      if (evar == id /*evar_id*/) {
        // Freshness depends only on plug, as all the free instances
        // of the requested variable are being substituted
        return plug->pattern_e_fresh(evar);
      }

      // Freshness depends on both input and plug,
      // as evar != evar_id (note that instances of evar_id
      // in pattern do not influence the result)
      return subpattern->pattern_e_fresh(evar) && plug->pattern_e_fresh(evar);
      break;

    case Instruction::SSubst:
      // Assume: substitution is well-formed => plug occurs in the result

      // We can skip checking evar == svar_id, because different types

      // Freshness depends on both input and plug,
      // as svar_id != evar (note that instances of evar_id
      // in pattern do not influence the result)
      return subpattern->pattern_e_fresh(evar) && plug->pattern_e_fresh(evar);
      break;

    default:
#if DEBUG
      throw std::runtime_error("pattern_e_fresh: not implemented: " +
                               std::to_string((int)inst));
#endif
      exit(1);
      break;
    }
  }

  bool pattern_s_fresh(Id svar) {
    switch (inst) {
    case Instruction::EVar:
      return true;
      break;
    case Instruction::SVar:
      return id != svar;
      break;
    case Instruction::Symbol:
      return true;
      break;
    case Instruction::MetaVar:
      return s_fresh->contains(svar);
      break;
    case Instruction::Implication:
      return left->pattern_s_fresh(svar) && right->pattern_s_fresh(svar);
      break;
    case Instruction::Application:
      return left->pattern_s_fresh(svar) && right->pattern_s_fresh(svar);
      break;
    case Instruction::Exists:
      return subpattern->pattern_s_fresh(svar);
      break;
    case Instruction::Mu:
      return (svar == id) || subpattern->pattern_s_fresh(svar);
      break;
    case Instruction::ESubst:
      // Assume: substitution is well-formed => plug occurs in the result

      // We can skip checking svar == evar_id, because different types

      // Freshness depends on both input and plug,
      // as evar_id != svar (note that instances of evar_id
      // in pattern do not influence the result)
      return subpattern->pattern_s_fresh(svar) && plug->pattern_s_fresh(svar);
      break;

    case Instruction::SSubst:
      // Assume: substitution is well-formed => plug occurs in the result
      if (svar == id /*svar_id*/) {
        // Freshness depends only on plug as all the free instances
        // of the requested variable are being substituted
        return plug->pattern_s_fresh(svar);
      }

      return subpattern->pattern_s_fresh(svar) && plug->pattern_s_fresh(svar);
      break;

    default:
#if DEBUG
      throw std::runtime_error("pattern_e_fresh: not implemented: " +
                               std::to_string((int)inst));
#endif
      exit(1);
      break;
    }
  }

  bool pattern_positive(Id svar) {
    switch (inst) {
    case Instruction::EVar:
      return true;
      break;
    case Instruction::SVar:
      return true;
      break;
    case Instruction::Symbol:
      return true;
      break;
    case Instruction::MetaVar:
      return positive->contains(svar);
      break;
    case Instruction::Implication:
      return left->pattern_negative(svar) && right->pattern_positive(svar);
      break;
    case Instruction::Application:
      return left->pattern_positive(svar) && right->pattern_positive(svar);
      break;
    case Instruction::Exists:
      return subpattern->pattern_positive(svar);
      break;
    case Instruction::Mu:
      return svar == id || subpattern->pattern_positive(svar);
      break;
    case Instruction::ESubst:
      // best-effort for now, see spec
      return subpattern->pattern_positive(svar) && plug->pattern_s_fresh(svar);
      break;
    case Instruction::SSubst: {
      auto plug_positive_svar =
          plug->pattern_s_fresh(svar) ||
          (subpattern->pattern_positive(id) && plug->pattern_positive(svar)) ||
          (subpattern->pattern_negative(id) && plug->pattern_negative(svar));

      if (svar == id) {
        return plug_positive_svar;
      }

      return subpattern->pattern_positive(svar) && plug_positive_svar;
      break;
    }
    default:
#if DEBUG
      throw std::runtime_error("pattern_positive: not implemented: " +
                               std::to_string((int)inst));
#endif
      exit(1);
      break;
    }
  }

  bool pattern_negative(Id svar) {
    switch (inst) {
    case Instruction::EVar:
      return true;
      break;
    case Instruction::SVar:
      return id != svar;
      break;
    case Instruction::Symbol:
      return true;
      break;
    case Instruction::MetaVar:
      return negative->contains(svar);
      break;
    case Instruction::Implication:
      return left->pattern_positive(svar) && right->pattern_negative(svar);
      break;
    case Instruction::Application:
      return left->pattern_negative(svar) && right->pattern_negative(svar);
      break;
    case Instruction::Exists:
      return subpattern->pattern_s_fresh(svar);
      break;
    case Instruction::Mu:
      return svar == id || subpattern->pattern_negative(svar);
      break;
    case Instruction::ESubst:
      // best-effort for now, see spec
      return subpattern->pattern_negative(svar) && plug->pattern_s_fresh(svar);
      break;
    case Instruction::SSubst: {
      auto plug_negative_svar =
          plug->pattern_s_fresh(svar) ||
          (subpattern->pattern_positive(id) && plug->pattern_negative(svar)) ||
          (subpattern->pattern_negative(id) && plug->pattern_positive(svar));

      if (svar == id) {
        return plug_negative_svar;
      }

      return subpattern->pattern_negative(svar) && plug_negative_svar;
      break;
    }
    default:
#if DEBUG
      throw std::runtime_error("pattern_negative: not implemented: " +
                               std::to_string((int)inst));
#endif
      exit(1);
      break;
    }
  }

  enum class TermType { Pattern, Proved };
  std::tuple<TermType, Pattern *> Term(TermType type, Pattern *pattern) {
    return std::make_tuple(type, pattern);
  }

  enum class EntryType { Pattern, Proved };
  std::tuple<EntryType, Pattern *> Entry(EntryType type, Pattern *pattern) {
    return std::make_tuple(type, pattern);
  }

  /// Pattern construction utilities
  /// ------------------------------
  static Pattern *evar(Id id) { return newPattern(Instruction::EVar, id); }

  static Pattern *svar(Id id) { return newPattern(Instruction::SVar, id); }

  static Pattern *symbol(Id id) { return newPattern(Instruction::Symbol, id); }

  static Pattern *metavar_unconstrained(Id id) {
    auto pattern = newPattern(Instruction::MetaVar, id);
    pattern->e_fresh = IdList::create();
    pattern->s_fresh = IdList::create();
    pattern->positive = IdList::create();
    pattern->negative = IdList::create();
    pattern->app_ctx_holes = IdList::create();
    return pattern;
  }

  static Pattern *metavar_s_fresh(Id id, Id s_fresh, IdList *positive,
                                  IdList *negative) {
    auto pattern = newPattern(Instruction::MetaVar, id);
    pattern->e_fresh = IdList::create();
    pattern->s_fresh = IdList::create(s_fresh);
    pattern->positive = positive;
    pattern->negative = negative;
    pattern->app_ctx_holes = IdList::create();
    ;
    return pattern;
  }

  static Pattern *exists(Id var, Pattern *subpattern) {
    auto pattern = newPattern(Instruction::Exists, var);
    pattern->subpattern = subpattern;
    return pattern;
  }

  static Pattern *mu(Id var, Pattern *subpattern) {
    auto pattern = newPattern(Instruction::Mu, var);
    pattern->subpattern = subpattern;
    return pattern;
  }

  static Pattern *esubst(Pattern *pattern, int evar_id, Pattern *plug) {
    auto evarPattern = newPattern(Instruction::ESubst, evar_id);
    evarPattern->subpattern = pattern;
    evarPattern->plug = plug;
    return evarPattern;
  }

  static Pattern *ssubst(Pattern *pattern, int svar_id, Pattern *plug) {
    auto svarPattern = newPattern(Instruction::SSubst, svar_id);
    svarPattern->subpattern = pattern;
    svarPattern->plug = plug;
    return svarPattern;
  }

  static Pattern *implies(Pattern *left, Pattern *right) {
    auto pattern = newPattern(Instruction::Implication, 0);
    pattern->left = left;
    pattern->right = right;
    return pattern;
  }

  static Pattern *app(Pattern *left, Pattern *right) {
    auto pattern = newPattern(Instruction::Application, 0);
    pattern->left = left;
    pattern->right = right;
    return pattern;
  }

  // Destructor to manually release memory
  static void destroyPattern(Pattern *pattern) {
    if (pattern) {
      if (pattern->left) {
        destroyPattern(pattern->left);
      }
      if (pattern->right) {
        destroyPattern(pattern->right);
      }
      if (pattern->subpattern) {
        destroyPattern(pattern->subpattern);
      }
      if (pattern->plug) {
        destroyPattern(pattern->plug);
      }
      if (pattern->e_fresh) {
        pattern->e_fresh->~LinkedList();
        free(pattern->e_fresh);
      }
      if (pattern->s_fresh) {
        pattern->s_fresh->~LinkedList();
        free(pattern->s_fresh);
      }
      if (pattern->positive) {
        pattern->positive->~LinkedList();
        free(pattern->positive);
      }
      if (pattern->negative) {
        pattern->negative->~LinkedList();
        free(pattern->negative);
      }
      if (pattern->app_ctx_holes) {
        pattern->app_ctx_holes->~LinkedList();
        free(pattern->app_ctx_holes);
      }
      free(pattern);
    }
  }

#if DEBUG
  void print() {
    switch (inst) {
    case Instruction::EVar:
      std::cout << "EVar(" << (int)id << ")";
      break;
    case Instruction::SVar:
      std::cout << "SVar(" << (int)id << ")";
      break;
    case Instruction::Symbol:
      std::cout << "Symbol(" << (int)id << ")";
      break;
    case Instruction::Implication:
      std::cout << "Implication(";
      left->print();
      std::cout << ", ";
      right->print();
      std::cout << ")";
      break;
    case Instruction::Application:
      std::cout << "Application(";
      left->print();
      std::cout << ", ";
      right->print();
      std::cout << ")";
      break;
    case Instruction::Exists:
      std::cout << "Exists(" << (int)id << ", ";
      subpattern->print();
      std::cout << ")";
      break;
    case Instruction::Mu:
      std::cout << "Mu(" << (int)id << ", ";
      subpattern->print();
      std::cout << ")";
      break;
    case Instruction::MetaVar:
      std::cout << "MetaVar(" << (int)id << ", ";
      e_fresh->print();
      std::cout << ", ";
      s_fresh->print();
      std::cout << ", ";
      positive->print();
      std::cout << ", ";
      negative->print();
      std::cout << ", ";
      app_ctx_holes->print();
      std::cout << ")";
      break;
    case Instruction::ESubst:
      std::cout << "ESubst(";
      subpattern->print();
      std::cout << ", " << (int)id << ", ";
      plug->print();
      std::cout << ")";
      break;
    case Instruction::SSubst:
      std::cout << "SSubst(";
      subpattern->print();
      std::cout << ", " << (int)id << ", ";
      plug->print();
      std::cout << ")";
      break;
    }
  }
#endif
};

int test_efresh(int a, int b) {
  const auto evar = Pattern::evar(a);

  auto left = Pattern::exists(a, Pattern::copy(evar));
  assert(left->pattern_e_fresh(a));

  auto right = Pattern::exists(b, Pattern::copy(evar));
  assert(!right->pattern_e_fresh(a));

  auto implication =
      Pattern::implies(Pattern::copy(left), Pattern::copy(right));
  assert(!implication->pattern_e_fresh(a));

  auto mvar =
      Pattern::metavar_s_fresh(a, b, IdList::create(b), IdList::create(b));
  auto metaapp = Pattern::app(Pattern::copy(left), Pattern::copy(mvar));
  assert(!metaapp->pattern_e_fresh(b));

  auto esubst = Pattern::esubst(Pattern::copy(right), a, Pattern::copy(left));
  assert(esubst->pattern_e_fresh(a));

  auto ssubst = Pattern::ssubst(Pattern::copy(right), a, Pattern::copy(left));
  assert(!ssubst->pattern_e_fresh(a));

#if DEBUG
  evar->print();
  std::cout << std::endl;
  left->print();
  std::cout << std::endl;
  right->print();
  std::cout << std::endl;
  implication->print();
  std::cout << std::endl;
  mvar->print();
  std::cout << std::endl;
  metaapp->print();
  std::cout << std::endl;
  esubst->print();
  std::cout << std::endl;
  ssubst->print();
  std::cout << std::endl;

#endif

  Pattern::destroyPattern(mvar);
  Pattern::destroyPattern(implication);
  Pattern::destroyPattern(left);
  Pattern::destroyPattern(right);
  Pattern::destroyPattern(evar);
  Pattern::destroyPattern(metaapp);
  Pattern::destroyPattern(esubst);
  Pattern::destroyPattern(ssubst);

  return 0;
}

int test_sfresh(int a, int b) {
  const auto svar = Pattern::svar(a);

  auto left = Pattern::mu(a, Pattern::copy(svar));
  assert(left->pattern_s_fresh(a));

  auto right = Pattern::mu(b, Pattern::copy(svar));
  assert(!right->pattern_s_fresh(a));

  auto implication =
      Pattern::implies(Pattern::copy(left), Pattern::copy(right));
  assert(!implication->pattern_s_fresh(a));

  auto mvar =
      Pattern::metavar_s_fresh(a, b, IdList::create(b), IdList::create(b));

  auto metaapp = Pattern::app(Pattern::copy(left), Pattern::copy(mvar));
  assert(!metaapp->pattern_s_fresh(a));

  auto metaapp2 = Pattern::app(Pattern::copy(left), Pattern::copy(mvar));
  assert(metaapp2->pattern_s_fresh(b));

  auto esubst = Pattern::esubst(Pattern::copy(right), a, Pattern::copy(left));
  assert(!esubst->pattern_s_fresh(a));

  auto ssubst = Pattern::ssubst(Pattern::copy(right), a, Pattern::copy(left));
  assert(ssubst->pattern_s_fresh(a));

#if DEBUG
  svar->print();
  std::cout << std::endl;
  left->print();
  std::cout << std::endl;
  right->print();
  std::cout << std::endl;
  implication->print();
  std::cout << std::endl;
  mvar->print();
  std::cout << std::endl;
  metaapp->print();
  std::cout << std::endl;
  metaapp2->print();
  std::cout << std::endl;
  esubst->print();
  std::cout << std::endl;
  ssubst->print();
  std::cout << std::endl;
#endif

  Pattern::destroyPattern(svar);
  Pattern::destroyPattern(left);
  Pattern::destroyPattern(right);
  Pattern::destroyPattern(implication);
  Pattern::destroyPattern(mvar);
  Pattern::destroyPattern(metaapp);
  Pattern::destroyPattern(metaapp2);
  Pattern::destroyPattern(esubst);
  Pattern::destroyPattern(ssubst);

  return 0;
}

int test_positivity() {
  auto X0 = Pattern::svar(0);
  auto X1 = Pattern::svar(1);
  auto X2 = Pattern::svar(2);
  auto c1 = Pattern::symbol(1);
  // auto neg_X1 = not(Pattern::copy(X1));

  // EVar
  auto evar1 = Pattern::evar(1);
  assert(evar1->pattern_positive(1));
  assert(evar1->pattern_negative(1));
  assert(evar1->pattern_positive(2));
  assert(evar1->pattern_negative(2));

  // SVar
  assert(X1->pattern_positive(1));
  assert(!X1->pattern_negative(1));
  assert(X1->pattern_positive(2));
  assert(X1->pattern_negative(2));

  // Symbol
  assert(c1->pattern_positive(1));
  assert(c1->pattern_negative(1));
  assert(c1->pattern_positive(2));
  assert(c1->pattern_negative(2));

  // Application
  auto appX1X2 = Pattern::app(Pattern::copy(X1), Pattern::copy(X2));
  assert(appX1X2->pattern_positive(1));
  assert(appX1X2->pattern_positive(2));
  assert(appX1X2->pattern_positive(3));
  assert(!appX1X2->pattern_negative(1));
  assert(!appX1X2->pattern_negative(2));
  assert(appX1X2->pattern_negative(3));

  // Implication
  auto impliesX1X2 = Pattern::implies(Pattern::copy(X1), Pattern::copy(X2));
  assert(!impliesX1X2->pattern_positive(1));
  assert(impliesX1X2->pattern_positive(2));
  assert(impliesX1X2->pattern_positive(3));
  assert(impliesX1X2->pattern_negative(1));
  assert(!impliesX1X2->pattern_negative(2));
  assert(impliesX1X2->pattern_negative(3));

  auto impliesX1X1 = Pattern::implies(Pattern::copy(X1), Pattern::copy(X1));
  assert(!impliesX1X1->pattern_positive(1));
  assert(!impliesX1X1->pattern_negative(1));

  // Exists
  auto existsX1X2 = Pattern::exists(1, Pattern::copy(X2));
  assert(existsX1X2->pattern_positive(1));
  assert(existsX1X2->pattern_positive(2));
  assert(existsX1X2->pattern_positive(3));
  assert(existsX1X2->pattern_negative(1));
  assert(!existsX1X2->pattern_negative(2));
  assert(existsX1X2->pattern_negative(3));

  // Mu
  auto muX1x1 = Pattern::mu(1, Pattern::copy(evar1));
  assert(muX1x1->pattern_positive(1));
  assert(muX1x1->pattern_positive(2));
  assert(muX1x1->pattern_negative(1));
  assert(muX1x1->pattern_negative(2));

  auto muX1X1 = Pattern::mu(1, Pattern::copy(X1));
  assert(muX1X1->pattern_positive(1));
  assert(muX1X1->pattern_negative(1));

  auto muX1X2 = Pattern::mu(1, Pattern::copy(X2));
  auto muX1impliesX2X1 =
      Pattern::mu(1, Pattern::implies(Pattern::copy(X2), Pattern::copy(X1)));
  assert(muX1X2->pattern_positive(1));
  assert(muX1X2->pattern_positive(2));
  assert(muX1X2->pattern_positive(3));
  assert(muX1X2->pattern_negative(1));
  assert(!muX1X2->pattern_negative(2));
  assert(muX1impliesX2X1->pattern_negative(2));
  assert(muX1X2->pattern_negative(3));

  // // MetaVar
  auto metavarUncons1 = Pattern::metavar_unconstrained(1);
  assert(!metavarUncons1->pattern_positive(1));
  assert(!metavarUncons1->pattern_positive(2));
  assert(!metavarUncons1->pattern_negative(1));
  assert(!metavarUncons1->pattern_negative(2));

  // Do not imply positivity from freshness
  auto metavarSFresh11__ =
      Pattern::metavar_s_fresh(1, 1, IdList::create(), IdList::create());
  auto metavarSFresh1111 =
      Pattern::metavar_s_fresh(1, 1, IdList::create(1), IdList::create(1));
  auto metavarSFresh111_ =
      Pattern::metavar_s_fresh(1, 1, IdList::create(1), IdList::create());
  auto metavarSFresh11_1 =
      Pattern::metavar_s_fresh(1, 1, IdList::create(), IdList::create(1));

  assert(!metavarSFresh11__->pattern_positive(1));
  assert(!metavarSFresh11__->pattern_negative(1));
  assert(metavarSFresh1111->pattern_positive(1));
  assert(metavarSFresh1111->pattern_negative(1));
  assert(metavarSFresh111_->pattern_positive(1));
  assert(metavarSFresh11_1->pattern_negative(1));

  assert(!metavarSFresh11__->pattern_positive(2));
  assert(!metavarSFresh11__->pattern_negative(2));

  // ESubst
  auto esubstMetaVarUnconsX0 =
      Pattern::esubst(Pattern::metavar_unconstrained(0), 0, Pattern::copy(X0));
  auto esubstMetaVarSFreshX1 = Pattern::esubst(
      Pattern::metavar_s_fresh(0, 1, IdList::create(1), IdList::create()), 0,
      Pattern::copy(X1));
  auto esubstMetaVarUnconsX1 =
      Pattern::esubst(Pattern::metavar_unconstrained(0), 0, Pattern::copy(X1));

  assert(!esubstMetaVarUnconsX0->pattern_positive(0));
  assert(!esubstMetaVarUnconsX1->pattern_positive(0));
  assert(!esubstMetaVarSFreshX1->pattern_positive(0));
  assert(!esubstMetaVarUnconsX0->pattern_negative(0));
  assert(!esubstMetaVarUnconsX1->pattern_negative(0));
  assert(!esubstMetaVarUnconsX1->pattern_negative(0));

  // SSubst
  auto ssubstMetaVarUnconsX0 =
      Pattern::ssubst(Pattern::metavar_unconstrained(0), 0, Pattern::copy(X0));
  auto ssubstMetaVarUnconsX1 =
      Pattern::ssubst(Pattern::metavar_unconstrained(0), 0, Pattern::copy(X1));
  auto ssubstMetaVarSFreshX1 = Pattern::ssubst(
      Pattern::metavar_s_fresh(0, 1, IdList::create(1), IdList::create()), 0,
      Pattern::copy(X1));

  assert(!ssubstMetaVarUnconsX0->pattern_positive(0));
  assert(ssubstMetaVarUnconsX1->pattern_positive(0));
  assert(ssubstMetaVarSFreshX1->pattern_positive(0));

  assert(!ssubstMetaVarUnconsX0->pattern_negative(0));
  assert(ssubstMetaVarUnconsX1->pattern_negative(0));
  assert(ssubstMetaVarSFreshX1->pattern_negative(0));

  // // Combinations
  // assert(!neg_X1->pattern_positive(1));
  // assert(neg_X1->pattern_positive(2));
  // assert(neg_X1->pattern_negative(1));
  // assert(neg_X1->pattern_negative(2));

  // auto negX1_implies_negX1 = implies(Pattern::copy(neg_X1),
  // Pattern::copy(neg_X1)); assert(!negX1_implies_negX1->pattern_positive(1));
  // assert(negX1_implies_negX1->pattern_positive(2));
  // assert(!negX1_implies_negX1->pattern_negative(1));
  // assert(negX1_implies_negX1->pattern_negative(2));

  // auto negX1_implies_X1 = implies(Pattern::copy(neg_X1), Pattern::copy(X1));
  // assert(negX1_implies_X1->pattern_positive(1));
  // assert(!negX1_implies_X1->pattern_negative(1));

#if DEBUG
  X0->print();
  std::cout << std::endl;
  X1->print();
  std::cout << std::endl;
  X2->print();
  std::cout << std::endl;
  c1->print();
  std::cout << std::endl;
  evar1->print();
  std::cout << std::endl;
  appX1X2->print();
  std::cout << std::endl;
  impliesX1X2->print();
  std::cout << std::endl;
  impliesX1X1->print();
  std::cout << std::endl;
  existsX1X2->print();
  std::cout << std::endl;
  muX1x1->print();
  std::cout << std::endl;
  muX1X1->print();
  std::cout << std::endl;
  muX1X2->print();
  std::cout << std::endl;
  muX1impliesX2X1->print();
  std::cout << std::endl;
  metavarUncons1->print();
  std::cout << std::endl;
  metavarSFresh11__->print();
  std::cout << std::endl;
  metavarSFresh1111->print();
  std::cout << std::endl;
  metavarSFresh111_->print();
  std::cout << std::endl;
  metavarSFresh11_1->print();
  std::cout << std::endl;
  esubstMetaVarUnconsX0->print();
  std::cout << std::endl;
  esubstMetaVarUnconsX1->print();
  std::cout << std::endl;
  esubstMetaVarSFreshX1->print();
  std::cout << std::endl;
  ssubstMetaVarUnconsX0->print();
  std::cout << std::endl;
  ssubstMetaVarUnconsX1->print();
  std::cout << std::endl;
  ssubstMetaVarSFreshX1->print();
  std::cout << std::endl;

#endif

  Pattern::destroyPattern(X0);
  Pattern::destroyPattern(X1);
  Pattern::destroyPattern(X2);
  Pattern::destroyPattern(c1);
  Pattern::destroyPattern(evar1);
  Pattern::destroyPattern(appX1X2);
  Pattern::destroyPattern(impliesX1X2);
  Pattern::destroyPattern(impliesX1X1);
  Pattern::destroyPattern(existsX1X2);
  Pattern::destroyPattern(muX1x1);
  Pattern::destroyPattern(muX1X1);
  Pattern::destroyPattern(muX1X2);
  Pattern::destroyPattern(muX1impliesX2X1);
  Pattern::destroyPattern(metavarUncons1);
  Pattern::destroyPattern(metavarSFresh11__);
  Pattern::destroyPattern(metavarSFresh1111);
  Pattern::destroyPattern(metavarSFresh111_);
  Pattern::destroyPattern(metavarSFresh11_1);
  Pattern::destroyPattern(esubstMetaVarUnconsX0);
  Pattern::destroyPattern(esubstMetaVarUnconsX1);
  Pattern::destroyPattern(esubstMetaVarSFreshX1);
  Pattern::destroyPattern(ssubstMetaVarUnconsX0);
  Pattern::destroyPattern(ssubstMetaVarUnconsX1);
  Pattern::destroyPattern(ssubstMetaVarSFreshX1);

  return 0;
}

[[circuit]] int foo(int a, int b) {
#if DEBUG
  std::cout << "Exeuting test_efresh(" << a << ", " << b << ")" << std::endl;
#endif
  test_efresh(a, b);
#if DEBUG
  std::cout << std::endl;
  std::cout << "Exeuting test_sfresh(" << a << ", " << b << ")" << std::endl;
#endif
  test_sfresh(a, b);
#if DEBUG
  std::cout << std::endl;
  std::cout << "Exeuting test_positivity()" << std::endl;
#endif
  test_positivity();

#if DEBUG
  //  evar->print();
  std::cout << std::endl;
#endif
  // Output: (A ∧ B) ∨ ¬C
  // Note: You would need to implement a print function to display it more
  // clearly
  return a + b * 3;
}

#if DEBUG
int main() { return foo(1, 2); }
#endif
