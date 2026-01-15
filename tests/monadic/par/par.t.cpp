// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <par.h>

#include <chrono>
#include <functional>
#include <future>
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

using namespace partest;

int main() {

  int runs = 3;

  auto before1 = std::chrono::high_resolution_clock::now();
  for(int i = 0; i < runs; i++) {
    fast(std::move(3),std::move(7));
  }
  auto after1 = std::chrono::high_resolution_clock::now();

  auto before2 = std::chrono::high_resolution_clock::now();
  for(int i = 0; i < runs; i++) {
    slow(std::move(3),std::move(7));
  }
  auto after2 = std::chrono::high_resolution_clock::now();

  std::chrono::duration<double> faster = (after2 - before2) - (after1 - before1);

  std::cout << "the concurrent code was " << faster << " faster!\n";
  return 0;
}

// clang++ -I. -std=c++23 par.o par.t.cpp -o par.t.o; ./par.t.o
