#include "lib.hpp"
#include <array>
#include <iostream>

#define MAX_SIZE_ASSUMPTION 27001
#define MAX_SIZE_CLAIM 27001
#define MAX_SIZE_PROOF 27001

typedef std::array<int, MAX_SIZE_ASSUMPTION> assumption_type;
typedef std::array<int, MAX_SIZE_CLAIM> claim_type;
typedef std::array<int, MAX_SIZE_PROOF> proof_type;

void read_input_assumption(assumption_type &arr, LinkedList<uint8_t> *input) {
  int arr_size = arr[0];
  for (int i = 1; i <= arr_size; i++) {
    input->push_back((uint8_t)arr[i]);
  }
}

void read_input_claim(claim_type &arr, LinkedList<uint8_t> *input) {
  int arr_size = arr[0];
  for (int i = 1; i <= arr_size; i++) {
    input->push_back((uint8_t)arr[i]);
  }
}

void read_input_proof(proof_type &arr, LinkedList<uint8_t> *input) {
  int arr_size = arr[0];
  for (int i = 1; i <= arr_size; i++) {
    input->push_back((uint8_t)arr[i]);
  }
}

#ifndef DEBUG
[[circuit]] int foo(assumption_type a, claim_type c, proof_type p) {

  auto gamma = LinkedList<uint8_t>::create();
  auto claim = LinkedList<uint8_t>::create();
  auto proof = LinkedList<uint8_t>::create();

  read_input_assumption(a, gamma);
  read_input_claim(c, claim);
  read_input_proof(p, proof);

  return Pattern::verify(gamma, claim, proof);
}
#else
int main() {
  assumption_type assumption = {0, 128};
  claim_type claim_gamma = {7, 137, 0, 137, 0, 5, 28, 30, 138};
  proof_type proof_gamma = {
      70,  137, 0,   137, 0,  137, 0,  5,  28,  5,   28, 29,  0,  137, 0,  // 15
      29,  0,   137, 0,   5,  5,   29, 2,  29,  0,   5,  137, 0,  29,  0,  // 15
      137, 0,   13,  26,  3,  2,   1,  0,  137, 0,   29, 0,   12, 26,  2,  // 15
      1,   0,   21,  28,  27, 27,  27, 29, 3,   137, 0,  137, 0,  12,  26, // 15
      2,   1,   0,   21,  28, 27,  27, 27, 29,  4,   30, 138};             // 12

  auto gamma = LinkedList<uint8_t>::create();
  auto claims = LinkedList<uint8_t>::create();
  auto proof = LinkedList<uint8_t>::create();

  read_input_assumption(assumption, gamma);
  read_input_claim(claim_gamma, claims);
  read_input_proof(proof_gamma, proof);

  std::cout << static_cast<int>(proof->get(proof->size()-1)) << std::endl;

  Pattern::verify(gamma, claims, proof);
  return 0;
}
#endif
