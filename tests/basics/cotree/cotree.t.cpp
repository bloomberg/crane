// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "cotree.h"

#include <iostream>
#include <vector>

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

// Helper: convert List to std::vector for easier comparison
std::vector<unsigned int>
to_vector(const List<unsigned int> &l) {
  std::vector<unsigned int> result;
  const List<unsigned int> *cur = &l;
  while (true) {
    auto ok = std::visit(
        Overloaded{[&](const List<unsigned int>::Nil) -> bool { return false; },
                   [&](const List<unsigned int>::Cons &args) -> bool {
                     result.push_back(args.d_a0);
                     cur = args.d_a1.get();
                     return true;
                   }},
        cur->v());
    if (!ok)
      break;
  }
  return result;
}

int main() {
  // Test 1: root of manually built cotree
  {
    ASSERT(Cotree::test_root == 1);
    std::cout << "Test 1 (root sample_cotree): PASSED" << std::endl;
  }

  // Test 2: comap_cotree doubles root
  {
    ASSERT(Cotree::test_doubled_root == 2);
    std::cout << "Test 2 (comap_cotree double): PASSED" << std::endl;
  }

  // Test 3: list_of_colist on infinite nats stream
  {
    auto vec = to_vector(Cotree::test_first_five);
    ASSERT(vec.size() == 5);
    ASSERT(vec[0] == 0);
    ASSERT(vec[1] == 1);
    ASSERT(vec[2] == 2);
    ASSERT(vec[3] == 3);
    ASSERT(vec[4] == 4);
    std::cout << "Test 3 (first 5 nats): PASSED" << std::endl;
  }

  // Test 4: root of unfolded infinite binary tree
  {
    ASSERT(Cotree::test_binary_root == 0);
    std::cout << "Test 4 (binary tree root): PASSED" << std::endl;
  }

  // Test 5: tree_of_cotree finite approximation root
  {
    ASSERT(Cotree::test_approx_root == 0);
    std::cout << "Test 5 (approx root): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll cotree tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
