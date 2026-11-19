// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <lazy_throw_twice.h>

#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>

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

// What calling [f] threw, or "" if it returned.
template <typename F> std::string thrown(F f) {
  try {
    f();
  } catch (const std::exception &e) {
    return e.what();
  }
  return "";
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  using L = LazyThrowTwice;

  // A generated suspension: the head of the second cell calls the axiom.
  {
    L::stream s = L::sample();
    ASSERT(L::hd(s) == 3u);
    L::stream t = L::tl(s);
    std::string first = thrown([&] { return L::hd(t); });
    std::string second = thrown([&] { return L::hd(t); });
    ASSERT(!first.empty());
    ASSERT(first == second);
  }

  // The runtime directly: a thunk that moves out of its capture, then
  // throws, runs once; every force rethrows its exception.
  {
    int runs = 0;
    auto held = std::make_shared<int>(7);
    auto l = crane::lazy<int>::delegate(
        [&runs, held = std::move(held)]() mutable -> int {
          ++runs;
          auto taken = std::move(held);
          if (!taken)
            return -1; // a second run would see the moved-from capture
          throw std::runtime_error("thunk threw");
        });
    std::string first = thrown([&] { return l.force(); });
    std::string second = thrown([&] { return l.force(); });
    crane::lazy<int> copy = l;
    std::string third = thrown([&] { return copy.force(); });
    ASSERT(first == "thunk threw");
    ASSERT(second == "thunk threw");
    ASSERT(third == "thunk threw");
    ASSERT(runs == 1);
  }

  // A thunk held in an [fn]: the same.
  {
    int runs = 0;
    crane::lazy<int> l(crane::fn<int()>([&runs]() -> int {
      ++runs;
      throw std::runtime_error("fn threw");
    }));
    std::string first = thrown([&] { return l.force(); });
    std::string second = thrown([&] { return l.force(); });
    ASSERT(first == "fn threw");
    ASSERT(second == "fn threw");
    ASSERT(runs == 1);
  }

  if (testStatus == 0)
    std::cout << "LazyThrowTwice test passed" << std::endl;
  return testStatus;
}
