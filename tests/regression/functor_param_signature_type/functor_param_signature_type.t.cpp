// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "functor_param_signature_type.h"

#include <iostream>

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

struct Sym {
  using terminal = int;
  static bool eqT(int a, int b) { return a == b; }
  using semty = int;
};

struct Params {
  using SymTy = Sym;
  using Defs = FunctorParamSignatureType::DefsFn<Sym>;
};

using Use = FunctorParamSignatureType::UseFn<Params>;

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  auto t = SigT<int, crane::obj>::existt(3, crane::obj(7));
  ASSERT(Use::same(t, 3));
  ASSERT(!Use::same(t, 4));

  if (testStatus == 0) {
    std::cout << "All functor_param_signature_type tests passed!" << std::endl;
  } else {
    std::cout << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
