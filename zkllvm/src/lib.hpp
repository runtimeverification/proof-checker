#include "../include/data_structures.hpp"
#include <cassert>
#include <cstring>
#include <iostream>
#include <memory>

enum class Instruction : uint8_t {
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
  CleanMetaVar = (uint8_t)(9 + 128),
  // EOF exclusive for zkLLVM
  NO_OP
};

Instruction from(uint8_t value) {
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
  case 138:
    return Instruction::NO_OP;
  default:
    exit(1); // Bad instruction!
  }
}

using Id = uint8_t;
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

  bool operator==(const Pattern &rhs) const {
    if (inst != rhs.inst || id != rhs.id) {
      return false;
    }
    if (left == nullptr && rhs.left != nullptr ||
        left != nullptr && rhs.left == nullptr) {
      return false;
    }
    if (right == nullptr && rhs.right != nullptr ||
        right != nullptr && rhs.right == nullptr) {
      return false;
    }
    if (subpattern == nullptr && rhs.subpattern != nullptr ||
        subpattern != nullptr && rhs.subpattern == nullptr) {
      return false;
    }
    if (plug == nullptr && rhs.plug != nullptr ||
        plug != nullptr && rhs.plug == nullptr) {
      return false;
    }
    if (e_fresh == nullptr && rhs.e_fresh != nullptr ||
        e_fresh != nullptr && rhs.e_fresh == nullptr) {
      return false;
    }
    if (s_fresh == nullptr && rhs.s_fresh != nullptr ||
        s_fresh != nullptr && rhs.s_fresh == nullptr) {
      return false;
    }
    if (positive == nullptr && rhs.positive != nullptr ||
        positive != nullptr && rhs.positive == nullptr) {
      return false;
    }
    if (negative == nullptr && rhs.negative != nullptr ||
        negative != nullptr && rhs.negative == nullptr) {
      return false;
    }
    if (app_ctx_holes == nullptr && rhs.app_ctx_holes != nullptr ||
        app_ctx_holes != nullptr && rhs.app_ctx_holes == nullptr) {
      return false;
    }
    if (left != nullptr && rhs.left != nullptr && *left != *rhs.left) {
      return false;
    }
    if (right != nullptr && rhs.right != nullptr && *right != *rhs.right) {
      return false;
    }
    if (subpattern != nullptr && rhs.subpattern != nullptr &&
        *subpattern != *rhs.subpattern) {
      return false;
    }
    if (plug != nullptr && rhs.plug != nullptr && *plug != *rhs.plug) {
      return false;
    }
    if (e_fresh != nullptr && rhs.e_fresh != nullptr &&
        *e_fresh != *rhs.e_fresh) {
      return false;
    }
    if (s_fresh != nullptr && rhs.s_fresh != nullptr &&
        *s_fresh != *rhs.s_fresh) {
      return false;
    }
    if (positive != nullptr && rhs.positive != nullptr &&
        *positive != *rhs.positive) {
      return false;
    }
    if (negative != nullptr && rhs.negative != nullptr &&
        *negative != *rhs.negative) {
      return false;
    }
    if (app_ctx_holes != nullptr && rhs.app_ctx_holes != nullptr &&
        *app_ctx_holes != *rhs.app_ctx_holes) {
      return false;
    }
    return true;
  }

  bool operator==(const Pattern *other) const { return *this == *other; }
  bool operator!=(const Pattern &rhs) { return !(*this == rhs); }

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
        copy->e_fresh->push_back(it->data);
      }
    }
    if (pattern->s_fresh) {
      copy->s_fresh = IdList::create();
      for (auto it = pattern->s_fresh->head; it; it = it->next) {
        copy->s_fresh->push_back(it->data);
      }
    }
    if (pattern->positive) {
      copy->positive = IdList::create();
      for (auto it = pattern->positive->head; it; it = it->next) {
        copy->positive->push_back(it->data);
      }
    }
    if (pattern->negative) {
      copy->negative = IdList::create();
      for (auto it = pattern->negative->head; it; it = it->next) {
        copy->negative->push_back(it->data);
      }
    }
    if (pattern->app_ctx_holes) {
      copy->app_ctx_holes = IdList::create();
      for (auto it = pattern->app_ctx_holes->head; it; it = it->next) {
        copy->app_ctx_holes->push_back(it->data);
      }
    }
    return copy;
  }

  bool pattern_e_fresh(Id evar) {
    switch (inst) {
    case Instruction::EVar:
      return evar != id;
    case Instruction::SVar:
    case Instruction::Symbol:
      return true;
    case Instruction::MetaVar:
      return e_fresh->contains(evar);
    case Instruction::Implication:
    case Instruction::Application:
      return left->pattern_e_fresh(evar) && right->pattern_e_fresh(evar);
    case Instruction::Exists:
      return (evar == id) || subpattern->pattern_e_fresh(evar);
    case Instruction::Mu:
      return subpattern->pattern_e_fresh(evar);
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

    case Instruction::SSubst:
      // Assume: substitution is well-formed => plug occurs in the result

      // We can skip checking evar == svar_id, because different types

      // Freshness depends on both input and plug,
      // as svar_id != evar (note that instances of evar_id
      // in pattern do not influence the result)
      return subpattern->pattern_e_fresh(evar) && plug->pattern_e_fresh(evar);

    default:
#if DEBUG
      throw std::runtime_error("pattern_e_fresh: not implemented: " +
                               std::to_string((int)inst));
#endif
      exit(1);
    }
  }

  bool pattern_s_fresh(Id svar) {
    switch (inst) {
    case Instruction::EVar:
      return true;
    case Instruction::SVar:
      return id != svar;
    case Instruction::Symbol:
      return true;
    case Instruction::MetaVar:
      return s_fresh->contains(svar);
    case Instruction::Implication:
    case Instruction::Application:
      return left->pattern_s_fresh(svar) && right->pattern_s_fresh(svar);
    case Instruction::Exists:
      return subpattern->pattern_s_fresh(svar);
    case Instruction::Mu:
      return (svar == id) || subpattern->pattern_s_fresh(svar);
    case Instruction::ESubst:
      // Assume: substitution is well-formed => plug occurs in the result

      // We can skip checking svar == evar_id, because different types

      // Freshness depends on both input and plug,
      // as evar_id != svar (note that instances of evar_id
      // in pattern do not influence the result)
      return subpattern->pattern_s_fresh(svar) && plug->pattern_s_fresh(svar);

    case Instruction::SSubst:
      // Assume: substitution is well-formed => plug occurs in the result
      if (svar == id /*svar_id*/) {
        // Freshness depends only on plug as all the free instances
        // of the requested variable are being substituted
        return plug->pattern_s_fresh(svar);
      }

      return subpattern->pattern_s_fresh(svar) && plug->pattern_s_fresh(svar);

    default:
#if DEBUG
      throw std::runtime_error("pattern_e_fresh: not implemented: " +
                               std::to_string((int)inst));
#endif
      exit(1);
    }
  }

  bool pattern_positive(Id svar) {
    switch (inst) {
    case Instruction::EVar:
    case Instruction::SVar:
    case Instruction::Symbol:
      return true;
    case Instruction::MetaVar:
      return positive->contains(svar);
    case Instruction::Implication:
      return left->pattern_negative(svar) && right->pattern_positive(svar);
    case Instruction::Application:
      return left->pattern_positive(svar) && right->pattern_positive(svar);
    case Instruction::Exists:
      return subpattern->pattern_positive(svar);
    case Instruction::Mu:
      return svar == id || subpattern->pattern_positive(svar);
    case Instruction::ESubst:
      // best-effort for now, see spec
      return subpattern->pattern_positive(svar) && plug->pattern_s_fresh(svar);
    case Instruction::SSubst: {
      auto plug_positive_svar =
          plug->pattern_s_fresh(svar) ||
          (subpattern->pattern_positive(id) && plug->pattern_positive(svar)) ||
          (subpattern->pattern_negative(id) && plug->pattern_negative(svar));

      if (svar == id) {
        return plug_positive_svar;
      }

      return subpattern->pattern_positive(svar) && plug_positive_svar;
    }
    default:
#if DEBUG
      throw std::runtime_error("pattern_positive: not implemented: " +
                               std::to_string((int)inst));
#endif
      exit(1);
    }
  }

  bool pattern_negative(Id svar) {
    switch (inst) {
    case Instruction::EVar:
      return true;
    case Instruction::SVar:
      return id != svar;
    case Instruction::Symbol:
      return true;
    case Instruction::MetaVar:
      return negative->contains(svar);
    case Instruction::Implication:
      return left->pattern_positive(svar) && right->pattern_negative(svar);
    case Instruction::Application:
      return left->pattern_negative(svar) && right->pattern_negative(svar);
    case Instruction::Exists:
      return subpattern->pattern_s_fresh(svar);
    case Instruction::Mu:
      return svar == id || subpattern->pattern_negative(svar);
    case Instruction::ESubst:
      // best-effort for now, see spec
      return subpattern->pattern_negative(svar) && plug->pattern_s_fresh(svar);
    case Instruction::SSubst: {
      auto plug_negative_svar =
          plug->pattern_s_fresh(svar) ||
          (subpattern->pattern_positive(id) && plug->pattern_negative(svar)) ||
          (subpattern->pattern_negative(id) && plug->pattern_positive(svar));

      if (svar == id) {
        return plug_negative_svar;
      }

      return subpattern->pattern_negative(svar) && plug_negative_svar;
    }
    default:
#if DEBUG
      throw std::runtime_error("pattern_negative: not implemented: " +
                               std::to_string((int)inst));
#endif
      exit(1);
    }
  }

  // Checks whether pattern is well-formed ASSUMING
  // that the sub-patterns are well-formed
  bool pattern_well_formed() {
    switch (inst) {
    case Instruction::MetaVar:
      return !app_ctx_holes->constainsElementOf(e_fresh);
    case Instruction::Mu:
      return subpattern->pattern_positive(id);
    case Instruction::ESubst:
      return !subpattern->pattern_e_fresh(id);
    case Instruction::SSubst:
      return !subpattern->pattern_s_fresh(id);
    default:
#if DEBUG
      throw std::runtime_error("Well-formedness checking is unimplemented yet "
                               "for this kind of pattern: " +
                               std::to_string((int)inst));
#endif
      exit(1);
    }
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

  static Pattern *metavar(Id id, IdList *e_fresh, IdList *s_fresh,
                          IdList *positive, IdList *negative,
                          IdList *app_ctx_holes) {
    auto pattern = newPattern(Instruction::MetaVar, id);
    pattern->e_fresh = e_fresh;
    pattern->s_fresh = s_fresh;
    pattern->positive = positive;
    pattern->negative = negative;
    pattern->app_ctx_holes = app_ctx_holes;
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
  ~Pattern() {
    if (left) {
      left->~Pattern();
    }
    if (right) {
      right->~Pattern();
    }
    if (subpattern) {
      subpattern->~Pattern();
    }
    if (plug) {
      plug->~Pattern();
    }
    if (e_fresh) {
      e_fresh->~LinkedList();
      free(e_fresh);
    }
    if (s_fresh) {
      s_fresh->~LinkedList();
      free(s_fresh);
    }
    if (positive) {
      positive->~LinkedList();
      free(positive);
    }
    if (negative) {
      negative->~LinkedList();
      free(negative);
    }
    if (app_ctx_holes) {
      app_ctx_holes->~LinkedList();
      free(app_ctx_holes);
    }
    free(this);
  }

  static void destroyPatterns(LinkedList<Pattern *> *patterns) {
    if (!patterns->empty()) {
      for (auto it : *patterns) {
        it->~Pattern();
      }
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
      /* std::cout << "Implication(";
       left->print();
       std::cout << ", ";
       right->print();
       std::cout << ")";*/
      std::cout << "(";
      left->print();
      std::cout << " -> ";
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
      // std::cout << "phi" << (int)id;
      std::cout << "MetaVar(" << (int)id;
      if (e_fresh->head) {
        std::cout << ", ";
        e_fresh->print();
      }
      if (s_fresh->head) {
        std::cout << ", ";
        s_fresh->print();
      }
      if (positive->head) {
        std::cout << ", ";
        positive->print();
      }
      if (negative->head) {
        std::cout << ", ";
        negative->print();
      }
      if (app_ctx_holes->head) {
        std::cout << ", ";
        app_ctx_holes->print();
      }
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

  class Term {
  public:
    enum class Type { Pattern, Proved };
    Type type;
    Pattern *pattern;
    Term(Type type, Pattern *pattern) : type(type), pattern(pattern) {}
    static Term *newTerm(Type type, Pattern *pattern) {
      auto term = static_cast<Term *>(malloc(sizeof(Term)));
      term->type = type;
      term->pattern = pattern;
      return term;
    }
    ~Term() {
      if (pattern) {
        pattern->~Pattern();
      }
      free(this);
    }

    bool operator==(const Term &rhs) const {
      if (type != rhs.type) {
        return false;
      }
      if (pattern == nullptr && rhs.pattern != nullptr ||
          pattern != nullptr && rhs.pattern == nullptr) {
        return false;
      }
      if (pattern != nullptr && rhs.pattern != nullptr &&
          *pattern != *rhs.pattern) {
        return false;
      }
      return true;
    }
    bool operator!=(const Term &rhs) const { return !(*this == rhs); }
  };

  class Entry {
  public:
    enum class Type { Pattern, Proved };
    Type type;
    Pattern *pattern;
    Entry(Type type, Pattern *pattern) : type(type), pattern(pattern) {}
    static Entry *newEntry(Type type, Pattern *pattern) {
      auto entry = static_cast<Entry *>(malloc(sizeof(Entry)));
      entry->type = type;
      entry->pattern = pattern;
      return entry;
    }
    ~Entry() {
      if (pattern) {
        pattern->~Pattern();
      }
      free(this);
    }
    bool operator==(const Entry &rhs) const {
      if (type != rhs.type) {
        return false;
      }
      if (pattern == nullptr && rhs.pattern != nullptr ||
          pattern != nullptr && rhs.pattern == nullptr) {
        return false;
      }
      if (pattern != nullptr && rhs.pattern != nullptr &&
          *pattern != *rhs.pattern) {
        return false;
      }
      return true;
    }
    bool operator!=(const Entry &rhs) const { return !(*this == rhs); }
  };

  // Notation
  static Pattern *bot() { return mu(0, svar(0)); }

  static Pattern *negate(Pattern *pattern) { // C++ doesn't accepted not
    return implies(pattern, bot());
  }

  static Pattern *forall(Id evar, Pattern *pattern) {
    return negate(exists(evar, negate(pattern)));
  }

  /// Substitution utilities
  /// ----------------------
  template <class Pattern> class Optional {
  private:
    Pattern *value;
    bool hasValue;

  public:
    Optional(Pattern *value) : value(value), hasValue(true) {}
    Optional(std::nullptr_t) : hasValue(false) {}
    Optional() : hasValue(false) { value = nullptr; }
    ~Optional() = default;

    operator bool() const { return hasValue; }

    // returns nullptr if hasValue is false
    Pattern *operator*() { return value; }
    Pattern *unwrap() { return value; }

    bool has_value() { return hasValue; }
  };

  static Optional<Pattern> instantiate_internal(Pattern &p, IdList &vars,
                                                LinkedList<Pattern *> &plugs) {
    switch (p.inst) {
    case Instruction::EVar:
    case Instruction::SVar:
    case Instruction::Symbol:
      return Optional<Pattern>();
    case Instruction::MetaVar: {
      Id pos = 0;
      for (auto it : vars) {
        if (it == p.id) {
          for (const auto &evar : *p.e_fresh) {
            if (!plugs[pos]->pattern_e_fresh(evar)) {
#ifdef DEBUG
              throw std::runtime_error("Instantiation of MetaVar " +
                                       std::to_string(p.id) +
                                       " breaks a freshness constraint: EVar " +
                                       std::to_string(evar));
#endif
              exit(1);
            }
          }
          for (const auto &svar : *p.s_fresh) {
            if (!plugs[pos]->pattern_s_fresh(svar)) {
#ifdef DEBUG
              throw std::runtime_error("Instantiation of MetaVar " +
                                       std::to_string(p.id) +
                                       " breaks a freshness constraint: SVar " +
                                       std::to_string(svar));
#endif
              exit(1);
            }
          }
          for (const auto &svar : *p.positive) {
            if (!plugs[pos]->pattern_positive(svar)) {
#ifdef DEBUG
              throw std::runtime_error(
                  "Instantiation of MetaVar " + std::to_string(p.id) +
                  " breaks a positivity constraint: SVar " +
                  std::to_string(svar));
#endif
              exit(1);
            }
          }
          for (const auto &svar : *p.negative) {
            if (!plugs[pos]->pattern_negative(svar)) {
#ifdef DEBUG
              throw std::runtime_error(
                  "Instantiation of MetaVar " + std::to_string(p.id) +
                  " breaks a negativity constraint: SVar " +
                  std::to_string(svar));
#endif
              exit(1);
            }
          }

          if (pos >= plugs.size()) {
#ifdef DEBUG
            throw std::runtime_error(
                "Substitution does not contain a corresponding value.");
#endif
            exit(1);
          }

          return Optional<Pattern>(copy(plugs[pos]));
        }
        pos++;
      }
      return Optional<Pattern>();
    }
    case Instruction::Implication: {
      Optional<Pattern> inst_left = instantiate_internal(*p.left, vars, plugs);
      Optional<Pattern> inst_right =
          instantiate_internal(*p.right, vars, plugs);

      if (!inst_left.has_value() && !inst_right.has_value()) {
        return Optional<Pattern>();
      } else {
        if (!inst_left.has_value()) {
          inst_left = Optional<Pattern>(copy(p.left)).unwrap();
        }
        if (!inst_right.has_value()) {
          inst_right = Optional<Pattern>(copy(p.right)).unwrap();
        }
        return Optional<Pattern>(
            implies(inst_left.unwrap(), inst_right.unwrap()));
      }
    }
    case Instruction::Application: {
      Optional<Pattern> inst_left = instantiate_internal(*p.left, vars, plugs);
      Optional<Pattern> inst_right =
          instantiate_internal(*p.right, vars, plugs);

      if (!inst_left.has_value() && !inst_right.has_value()) {
        return Optional<Pattern>();
      } else {
        if (!inst_left.has_value()) {
          inst_left = Optional<Pattern>(copy(p.left));
        }
        if (!inst_right.has_value()) {
          inst_right = Optional<Pattern>(copy(p.right));
        }
        return Optional<Pattern>(app(inst_left.unwrap(), inst_right.unwrap()));
      }
    }
    case Instruction::Exists: {
      Optional<Pattern> inst_sub =
          instantiate_internal(*p.subpattern, vars, plugs);
      if (!inst_sub.has_value()) {
        return Optional<Pattern>();
      } else {
        if (!inst_sub.has_value()) {
          inst_sub = Optional<Pattern>(copy(p.subpattern));
        }
        return Optional<Pattern>(exists(p.id, inst_sub.unwrap()));
      }
    }
    case Instruction::Mu: {
      Optional<Pattern> inst_sub =
          instantiate_internal(*p.subpattern, vars, plugs);
      if (!inst_sub.has_value()) {
        return Optional<Pattern>();
      } else {
        if (!inst_sub.has_value()) {
          inst_sub = Optional<Pattern>(copy(p.subpattern));
        }
        return Optional<Pattern>(mu(p.id, inst_sub.unwrap()));
      }
    }
    case Instruction::ESubst: {
      Optional<Pattern> inst_pattern =
          instantiate_internal(*p.subpattern, vars, plugs);
      Optional<Pattern> inst_plug = instantiate_internal(*p.plug, vars, plugs);
      if (!inst_pattern.has_value() && !inst_plug.has_value()) {
        return Optional<Pattern>();
      } else {
        if (!inst_pattern.has_value()) {
          inst_pattern = Optional<Pattern>(copy(p.subpattern));
        }
        if (!inst_plug.has_value()) {
          inst_plug = Optional<Pattern>(copy(p.plug));
        }
        return Optional<Pattern>(
            esubst(inst_pattern.unwrap(), p.id, inst_plug.unwrap()));
      }
    }
    case Instruction::SSubst: {
      Optional<Pattern> inst_pattern =
          instantiate_internal(*p.subpattern, vars, plugs);
      Optional<Pattern> inst_plug = instantiate_internal(*p.plug, vars, plugs);
      if (!inst_pattern.has_value() && !inst_plug.has_value()) {
        return Optional<Pattern>();
      } else {
        if (!inst_pattern.has_value()) {
          inst_pattern = Optional<Pattern>(copy(p.subpattern));
        }
        if (!inst_plug.has_value()) {
          inst_plug = Optional<Pattern>(copy(p.plug));
        }
        return Optional<Pattern>(
            ssubst(inst_pattern.unwrap(), p.id, inst_plug.unwrap()));
      }
    }
    default:
      return Optional<Pattern>();
    }
  }

  static void instantiate_in_place(Pattern &p, IdList &vars,
                                   LinkedList<Pattern *> &plugs) {
    if (auto ret = instantiate_internal(p, vars, plugs)) {
      p = *copy(ret.unwrap()); // FIXME: We shouldn't have to copy here
    }
  }

  /// Proof checker
  /// =============

  typedef LinkedList<Term *> Stack;
  typedef LinkedList<Pattern *> Claims;
  typedef LinkedList<Entry *> Memory;

  /// Stack utilities
  /// ---------------

  static Term *pop_stack(Stack *stack) { return stack->pop(); }

  static Pattern *pop_stack_pattern(Stack *stack) {
    auto term = pop_stack(stack);
    if (term->type != Term::Type::Pattern) {
#if DEBUG
      throw std::runtime_error("Expected pattern on the stack.");
#endif
      exit(1);
    }
    return term->pattern;
  }

  static Pattern *pop_stack_proved(Stack *stack) {
    auto term = pop_stack(stack);
    if (term->type != Term::Type::Proved) {
#if DEBUG
      throw std::runtime_error("Expected proved on the stack.");
#endif
      exit(1);
    }
    return term->pattern;
  }

  /// Main implementation
  /// -------------------

  enum class ExecutionPhase { Gamma, Claims, Proof };

  static LinkedList<uint8_t> *
  read_u8_vec(LinkedList<uint8_t>::Iterator &iterator) {
    auto size = *iterator.next();
    auto vec = LinkedList<uint8_t>::create();
    for (int i = 0; i < size; i++) {
      vec->push_back(*iterator.next());
    }
    return vec;
  }

  static void execute_instructions(LinkedList<uint8_t> *buffer, Stack *stack,
                                   Memory *memory, Claims *claims,
                                   ExecutionPhase phase) {
    // Get an iterator for the input buffer
    auto iterator = buffer->begin();

    // Metavars
    // Phi0 = MetaVar(0)
    // Phi1 = MetaVar(1)
    // Phi2 = MetaVar(2)
    auto phi0 = metavar_unconstrained(0);
    auto phi1 = metavar_unconstrained(1);
    auto phi2 = metavar_unconstrained(2);

    // Axioms
    // Prop1: phi0 => (phi1 => phi0)
    // Prop2: (phi0 => (phi1 => phi2)) => ((phi0 => phi1) => (phi0 => phi2))
    // Prop3: (~phi0 => phi0
    auto prop1 = implies(copy(phi0), implies(copy(phi1), copy(phi0)));
    auto prop2 =
        implies(implies(copy(phi0), implies(copy(phi1), copy(phi2))),
                implies(implies(copy(phi0), phi1), implies(copy(phi0), phi2)));
    auto prop3 = implies(negate(negate(copy(phi0))), copy(phi0));

    // Quantifier: forall x. phi0
    auto quantifier = implies(esubst(copy(phi0), 0, evar(1)), exists(0, phi0));

    // Existence: exists x. phi0
    auto existence = exists(0, phi0);

    // Iteration through the input buffer
    while (iterator != buffer->end()) {
      Instruction instr_u32 = from(*iterator.next());

      switch (instr_u32) {
        // TODO: Add an abstraction for pushing these one-argument terms on
        // stack?
      case Instruction::EVar:
      case Instruction::SVar:
      case Instruction::Symbol:
      case Instruction::MetaVar: {
        auto getId = iterator.next();
        if (getId == buffer->end()) {
#if DEBUG
          throw std::runtime_error("Expected id for MetaVar instruction");
#endif
          exit(1);
        }
        auto id = (Id)*getId;

        auto e_fresh = read_u8_vec(iterator);
        auto s_fresh = read_u8_vec(iterator);
        auto positive = read_u8_vec(iterator);
        auto negative = read_u8_vec(iterator);
        auto app_ctx_holes = read_u8_vec(iterator);

        auto metavar_pat =
            metavar(id, e_fresh, s_fresh, positive, negative, app_ctx_holes);

        if (!metavar_pat->pattern_well_formed()) {
#if DEBUG
          throw std::runtime_error("Constructed meta-var " +
                                   std::to_string(id) + " is ill-formed.");
#endif
          exit(1);
        }
        stack->push(Term::newTerm(Term::Type::Pattern, metavar_pat));
        break;
      }
      case Instruction::CleanMetaVar:
        break;
      case Instruction::Implication: {
        auto right = pop_stack_pattern(stack);
        auto left = pop_stack_pattern(stack);
        stack->push(Term::newTerm(Term::Type::Pattern, implies(left, right)));
        break;
      }
      case Instruction::Application:
      case Instruction::Exists:
      case Instruction::Mu:
      case Instruction::ESubst:
      case Instruction::SSubst:
      case Instruction::Prop1:
        stack->push(Term::newTerm(Term::Type::Proved, copy(prop1)));
        break;
      case Instruction::Prop2:
        stack->push(Term::newTerm(Term::Type::Proved, copy(prop2)));
        break;
      case Instruction::Prop3:
        stack->push(Term::newTerm(Term::Type::Proved, copy(prop3)));
        break;
      case Instruction::ModusPonens:
      case Instruction::Quantifier:
      case Instruction::Generalization:
      case Instruction::Existence:
      case Instruction::Substitution:
      case Instruction::Instantiate: {
        auto n = iterator.next();
        if (n == buffer->end()) {
#if DEBUG
          throw std::runtime_error(
              "Insufficient parameters for Instantiate instruction");
#endif
          exit(1);
        }
        auto ids = LinkedList<Id>::create();
        auto plugs = LinkedList<Pattern *>::create();

        auto metaterm = pop_stack(stack);
        for (int i = 0; i < *n; i++) {
          ids->push(*iterator.next());
          plugs->push(pop_stack_pattern(stack));
        }

        if (metaterm->type == Term::Type::Pattern) {
          instantiate_in_place(*metaterm->pattern, *ids, *plugs);
          stack->push(
              Term::newTerm(Term::Type::Pattern, copy(metaterm->pattern)));
        } else if (metaterm->type == Term::Type::Proved) {
          instantiate_in_place(*metaterm->pattern, *ids, *plugs);
          stack->push(
              Term::newTerm(Term::Type::Proved, copy(metaterm->pattern)));
        } else {
#if DEBUG
          throw std::runtime_error("Instantiate needs a term on the stack");
#endif
          exit(1);
        }
        break;
      }
      case Instruction::Pop:
        break;
      case Instruction::Save: {
        auto term = stack->front();
        if (term->type == Term::Type::Pattern) {
          memory->push_back(
              Entry::newEntry(Entry::Type::Pattern, copy(term->pattern)));
        } else if (term->type == Term::Type::Proved) {
          memory->push_back(
              Entry::newEntry(Entry::Type::Proved, copy(term->pattern)));
        } else {
#if DEBUG
          throw std::runtime_error("Save needs an entry on the stack");
#endif
          exit(1);
        }
        break;
      }
      case Instruction::Load: {
        auto index = iterator.next();
        if (index == buffer->end()) {
#if DEBUG
          throw std::runtime_error(
              "Insufficient parameters for Load instruction");
#endif
          exit(1);
        }
        Entry *entry = memory->get(*index);
        if (entry->type == Entry::Type::Pattern) {
          stack->push(Term::newTerm(Term::Type::Pattern, copy(entry->pattern)));
        } else if (entry->type == Entry::Type::Proved) {
          stack->push(Term::newTerm(Term::Type::Proved, copy(entry->pattern)));
        } else {
#if DEBUG
          throw std::runtime_error("Load needs an entry in memory");
#endif
          exit(1);
        }
        break;
      }
      case Instruction::Publish:
      default: {
#if DEBUG
        throw std::runtime_error("Unknown instruction: " +
                                 std::to_string((int)instr_u32));
#endif
        exit(1);
      }
      }
    }
  }
};