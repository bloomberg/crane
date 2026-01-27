// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <nat_bde.h>

#include <bdlf_overloaded.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_string.h>
#include <bsl_variant.h>

using namespace BloombergLP;

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        bsl::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << bsl::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);

bsl::shared_ptr<Nat::nat> int_to_nat(int x) {
  if (x <= 0) {
    return Nat::nat::ctor::O_();
  }
  else {
    return Nat::nat::ctor::S_(int_to_nat(x-1));
  }
}

int main() {

  ASSERT(5 == int_to_nat(5)->nat_to_int());
  ASSERT(9 == int_to_nat(5)->add(int_to_nat(4))->nat_to_int());

  bsl::cout << "hello from BDE!\n";

  return 0;
}

/*
  clang++ -c -std=c++20 -Wno-deprecated-literal-operator -Wno-unused-command-line-argument \
  -I. -I../../theories/cpp -I~/bde_install/include \
  nat_bde.cpp \
  -L~/bde_install/lib \
  -lbsl -lbal -lbdl -lbbl -lbbryu -linteldfp -lpcre2 \
  -o nat_bde.o

  clang++ -std=c++20 -Wno-deprecated-literal-operator -Wno-unused-command-line-argument \
  -I. -I../../theories/cpp -I~/bde_install/include \
  nat_bde.o nat_bde.t.cpp \
  -L~/bde_install/lib \
  -lbsl -lbal -lbdl -lbbl -lbbryu -linteldfp -lpcre2 \
  -o nat_bde.t.exe
*/
