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

  // Checks whether pattern is well-formed ASSUMING
  // that the sub-patterns are well-formed
  bool pattern_well_formed() {
    switch (inst) {
    case Instruction::MetaVar:
      return !app_ctx_holes->isDisjoint(e_fresh);
      break;
    case Instruction::Mu:
      return subpattern->pattern_positive(id);
      break;
    case Instruction::ESubst:
      return !subpattern->pattern_e_fresh(id);
      break;
    case Instruction::SSubst:
      return !subpattern->pattern_s_fresh(id);
      break;
    default:
#if DEBUG
      throw std::runtime_error("Well-formedness checking is unimplemented yet "
                               "for this kind of pattern: " +
                               std::to_string((int)inst));
#endif
      exit(1);
      break;
    }
  }
  enum class TermType { Pattern, Proved };
  typedef std::tuple<TermType, Pattern *> Term;
  Term CreateTerm(TermType type, Pattern *pattern) {
    return std::make_tuple(type, pattern);
  }

  enum class EntryType { Pattern, Proved };
  typedef std::tuple<EntryType, Pattern *> Entry;
  Entry CreateEntry(EntryType type, Pattern *pattern) {
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

  // Notation
  static Pattern *bot() { return Pattern::mu(0, Pattern::svar(0)); }

  static Pattern *negate(Pattern *pattern) { // C++ doesn't accepted not
    return Pattern::implies(pattern, Pattern::bot());
  }

  static Pattern *forall(Id evar, Pattern *pattern) {
    return Pattern::negate(Pattern::exists(evar, Pattern::negate(pattern)));
  }

  /// Proof checker
  /// =============

  typedef LinkedList<Term *> Stack;
  typedef LinkedList<Pattern *> Claims;
  typedef LinkedList<Entry *> Memory;

  /// Stack utilities
  /// ---------------

  Term *pop_stack(Stack *stack) { return stack->pop(); }

  Pattern *pop_stack_pattern(Stack *stack) {
    auto term = stack->pop();
    if (std::get<0>(*term) != TermType::Pattern) {
      throw std::runtime_error("Expected pattern on the stack.");
    }
    return std::get<1>(*term);
  }

  Pattern *pop_stack_proved(Stack *stack) {
    auto term = stack->pop();
    if (std::get<0>(*term) != TermType::Proved) {
      throw std::runtime_error("Expected proved on the stack.");
    }
    return std::get<1>(*term);
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
