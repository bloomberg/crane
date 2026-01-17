// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <nat.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        std::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << std::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);


std::shared_ptr<Nat::nat> int_to_nat(int x) {
  if (x <= 0) {
    return Nat::nat::ctor::O_();
  }
  else {
    return Nat::nat::ctor::S_(int_to_nat(x-1));
  }
}

int main() {

  // Functions are now methods on the eponymous nat type
  ASSERT(5 == int_to_nat(5)->nat_to_int());
  ASSERT(9 == int_to_nat(5)->add(int_to_nat(4))->nat_to_int());

  return 0;
}

// clang++ -I. -I~/crane/theories/cpp -std=c++23 -O2 nat.o nat.t.cpp -o nat.t.o; ./nat.t.o
