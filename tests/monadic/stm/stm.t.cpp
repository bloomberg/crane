// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <stm.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

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

int main() {
  auto x = stmtest::io_inc(4);
  std::cout << std::to_string(x) << '\n';
  // auto p = io_transfer_test(23, 32, 8);
  // std::cout << p.first << ", " << p.second << '\n';
  return 0;
}

// clang++ -I. -I ../../theories/cpp -std=c++23 stm.cpp stm.t.cpp -o stm.t.exe; ./stm.t.exe
