// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <top_bde.h>

#include <bdlf_overloaded.h>
#include <bsl_algorithm.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_string.h>
#include <bsl_utility.h>
#include <bsl_variant.h>

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

using namespace std;

int main() {
  /*
  shared_ptr<list::list<shared_ptr<prod::prod<int, int>>>> g1 =
    list::cons<shared_ptr<prod::prod<int, int>>>::make(prod::pair<int, int>::make(0, 1),
    list::cons<shared_ptr<prod::prod<int, int>>>::make(prod::pair<int, int>::make(0, 2),
    list::cons<shared_ptr<prod::prod<int, int>>>::make(prod::pair<int, int>::make(1, 2),
    list::nil<shared_ptr<prod::prod<int, int>>>::make())));

  shared_ptr<list::list<pair<int, int>>> g1 =
    list::cons<pair<int, int>>::make(make_pair(0, 1),
    list::cons<pair<int, int>>::make(make_pair(0, 2),
    list::cons<pair<int, int>>::make(make_pair(1, 2),
				     list::nil<pair<int, int>>::make())));
  std::shared_ptr<list::list<std::shared_ptr<list::list<int>>>> r1 =
    topological_sort<int>(std::move([](int a, int b) { return a == b; }), std::move(g1));

  std::cout
      << list_to_string<std::shared_ptr<list::list<int>>>(std::move(
            [](std::shared_ptr<list::list<int>> l) {
                return list_to_string<int>(std::move([](int x) { return std::to_string(x); }), std::move(l));
            }), std::move(r1))
      << std::endl; */

// std::cout << test(std::move(unit::tt::make())) << std::endl;
  return 0;
}

// clang++ -I. -std=c++23 -O2 top.o top.t.cpp -o top.t.o; ./top.t.o
