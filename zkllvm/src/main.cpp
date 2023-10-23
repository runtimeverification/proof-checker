#include "../tests/unit_tests.hpp"
#include <iostream>

#ifndef DEBUG
typedef __attribute__((ext_vector_type(1))) int assumption_type;
typedef __attribute__((ext_vector_type(1))) int claim_type;
typedef __attribute__((ext_vector_type(1))) int proof_type;

[[circuit]] int foo(assumption_type a, claim_type c, proof_type p) {

  int x = 1;
  int y = 2;
  test_efresh(x, y);
  test_sfresh(x, y);
  test_positivity();
  test_wellformedness_positive();
  test_instantiate();
  test_construct_phi_implies_phi();
  test_phi_implies_phi_impl();

  return c[0];
}
#else
int main() {
  int x = 1;
  int y = 2;

  std::cout << "Executing test_efresh(" << x << ", " << y << ")" << std::endl;
  test_efresh(x, y);
  std::cout << std::endl;

  std::cout << "Executing test_sfresh(" << x << ", " << y << ")" << std::endl;
  test_sfresh(x, y);
  std::cout << std::endl;

  std::cout << "Executing test_positivity()" << std::endl;
  test_positivity();
  std::cout << std::endl;

  std::cout << "Executing test_wellformedness_positive()" << std::endl;
  test_wellformedness_positive();
  std::cout << std::endl;

  std::cout << "Executing test_instantiate()" << std::endl;
  test_instantiate();
  std::cout << std::endl;

  std::cout << "Executing test_construct_phi_implies_phi()" << std::endl;
  test_construct_phi_implies_phi();
  std::cout << std::endl;

  std::cout << "Executing test_phi_implies_phi_impl()" << std::endl;
  test_phi_implies_phi_impl();
  std::cout << std::endl;

  return 0;
}
#endif
