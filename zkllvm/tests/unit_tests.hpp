#include "../src/lib.hpp"

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

 mvar->~Pattern();
 implication->~Pattern();
 left->~Pattern();
 right->~Pattern();
 evar->~Pattern();
 metaapp->~Pattern();
 esubst->~Pattern();
 ssubst->~Pattern();

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

  svar->~Pattern();
  left->~Pattern();
  right->~Pattern();
  implication->~Pattern();
  mvar->~Pattern();
  metaapp->~Pattern();
  metaapp2->~Pattern();
  esubst->~Pattern();
  ssubst->~Pattern();

  return 0;
}

int test_positivity() {
  auto X0 = Pattern::svar(0);
  auto X1 = Pattern::svar(1);
  auto X2 = Pattern::svar(2);
  auto c1 = Pattern::symbol(1);
  auto neg_X1 = Pattern::negate(Pattern::copy(X1));

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

  // MetaVar
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

  // Combinations
  assert(!neg_X1->pattern_positive(1));
  assert(neg_X1->pattern_positive(2));
  assert(neg_X1->pattern_negative(1));
  assert(neg_X1->pattern_negative(2));

  auto negX1_implies_negX1 =
      Pattern::implies(Pattern::copy(neg_X1), Pattern::copy(neg_X1));
  assert(!negX1_implies_negX1->pattern_positive(1));
  assert(negX1_implies_negX1->pattern_positive(2));
  assert(!negX1_implies_negX1->pattern_negative(1));
  assert(negX1_implies_negX1->pattern_negative(2));

  auto negX1_implies_X1 =
      Pattern::implies(Pattern::copy(neg_X1), Pattern::copy(X1));
  assert(negX1_implies_X1->pattern_positive(1));
  assert(!negX1_implies_X1->pattern_negative(1));

#if DEBUG
  X0->print();
  std::cout << std::endl;
  X1->print();
  std::cout << std::endl;
  X2->print();
  std::cout << std::endl;
  c1->print();
  std::cout << std::endl;
  neg_X1->print();
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
  negX1_implies_negX1->print();
  std::cout << std::endl;
  negX1_implies_X1->print();
  std::cout << std::endl;

#endif

  X0->~Pattern();
  X1->~Pattern();
  X2->~Pattern();
  c1->~Pattern();
  neg_X1->~Pattern();
  evar1->~Pattern();
  appX1X2->~Pattern();
  impliesX1X2->~Pattern();
  impliesX1X1->~Pattern();
  existsX1X2->~Pattern();
  muX1x1->~Pattern();
  muX1X1->~Pattern();
  muX1X2->~Pattern();
  muX1impliesX2X1->~Pattern();
  metavarUncons1->~Pattern();
  metavarSFresh11__->~Pattern();
  metavarSFresh1111->~Pattern();
  metavarSFresh111_->~Pattern();
  metavarSFresh11_1->~Pattern();
  esubstMetaVarUnconsX0->~Pattern();
  esubstMetaVarUnconsX1->~Pattern();
  esubstMetaVarSFreshX1->~Pattern();
  ssubstMetaVarUnconsX0->~Pattern();
  ssubstMetaVarUnconsX1->~Pattern();
  ssubstMetaVarSFreshX1->~Pattern();
  negX1_implies_negX1->~Pattern();
  negX1_implies_X1->~Pattern();

  return 0;
}

int test_wellformedness_positive() {
  auto svar = Pattern::svar(1);
  auto mux_x = Pattern::mu(1, Pattern::copy(svar));
  assert(mux_x->pattern_well_formed());

  auto mux_x2 = Pattern::mu(2, Pattern::negate(Pattern::copy(svar)));
  assert(mux_x2->pattern_well_formed());

  auto mux_x3 = Pattern::mu(2, Pattern::negate(Pattern::symbol(1)));
  assert(mux_x3->pattern_well_formed());

  auto mux_x4 = Pattern::mu(1, Pattern::negate(Pattern::copy(svar)));
  assert(!mux_x4->pattern_well_formed());

  auto phi = Pattern::metavar_s_fresh(97, 2, IdList::create(), IdList::create());
  auto mux_phi = Pattern::mu(1, Pattern::copy(phi));
  assert(!mux_phi->pattern_well_formed());

  // Even though freshness implies positivity, we do not want to do any
  // additional reasoning and let everything on the prover
  auto phi2 =
      Pattern::metavar_s_fresh(98, 1, IdList::create(), IdList::create());
  auto mux_phi2 = Pattern::mu(1, Pattern::copy(phi2));
  assert(!mux_phi2->pattern_well_formed());

  // It's ok if 2 is negative, the only thing we care about is that 2 is
  // guaranteed to be positive (we can instantiate without this variable)
  auto phi3 = Pattern::metavar_s_fresh(99, 1, IdList::create(2),
                                       IdList::create(2));
  auto mux_phi3 = Pattern::mu(2, Pattern::copy(phi3));
  assert(mux_phi3->pattern_well_formed());

  auto phi4 = Pattern::metavar_s_fresh(100, 1, IdList::create(2),
                                       IdList::create());
  auto mux_phi4 = Pattern::mu(2, Pattern::copy(phi4));
  assert(mux_phi4->pattern_well_formed());

  #if DEBUG
  svar->print();
  std::cout << std::endl;
  mux_x->print();
  std::cout << std::endl;
  mux_x2->print();
  std::cout << std::endl;
  mux_x3->print();
  std::cout << std::endl;
  mux_x4->print();
  std::cout << std::endl;
  phi->print();
  std::cout << std::endl;
  mux_phi->print();
  std::cout << std::endl;
  phi2->print();
  std::cout << std::endl;
  mux_phi2->print();
  std::cout << std::endl;
  phi3->print();
  std::cout << std::endl;
  mux_phi3->print();
  std::cout << std::endl;
  phi4->print();
  std::cout << std::endl;
  mux_phi4->print();
  std::cout << std::endl;
  #endif

  svar->~Pattern();
  mux_x->~Pattern();
  mux_x2->~Pattern();
  mux_x3->~Pattern();
  mux_x4->~Pattern();
  phi->~Pattern();
  mux_phi->~Pattern();
  phi2->~Pattern();
  mux_phi2->~Pattern();
  phi3->~Pattern();
  mux_phi3->~Pattern();
  phi4->~Pattern();
  mux_phi4->~Pattern();

  return 0;
}