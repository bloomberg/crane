// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <functional>
#include <iostream>
#include <loopify_tmc.h>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100)
      ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

// Helper: convert list to vector for easy comparison
template <typename T>
std::vector<T> to_vec(const LoopifyTmc::list<T> &l) {
  std::vector<T> result;
  const LoopifyTmc::list<T> *cur = &l;
  while (std::holds_alternative<typename LoopifyTmc::list<T>::Cons>(cur->v())) {
    auto &c = std::get<typename LoopifyTmc::list<T>::Cons>(cur->v());
    result.push_back(c.d_a0);
    cur = c.d_a1.get();
  }
  return result;
}

// Helper: build list from vector
template <typename T>
LoopifyTmc::list<T> from_vec(const std::vector<T> &v) {
  using List = LoopifyTmc::list<T>;
  auto result = List::nil();
  for (int i = v.size() - 1; i >= 0; --i) {
    result = List::cons(v[i], std::move(result));
  }
  return result;
}

int main() {
  using List = LoopifyTmc::list<unsigned int>;

  // Build test lists
  auto l3 = from_vec<unsigned int>({1, 2, 3});
  auto l5 = from_vec<unsigned int>({4, 5, 6, 7, 8});
  auto empty = List::nil();

  // ===== app =====
  {
    auto result = LoopifyTmc::app(l3, l5);
    auto v = to_vec(result);
    ASSERT(v.size() == 8);
    ASSERT(v[0] == 1 && v[1] == 2 && v[2] == 3);
    ASSERT(v[3] == 4 && v[7] == 8);

    // app with empty
    auto r2 = LoopifyTmc::app(empty, l3);
    ASSERT(to_vec(r2) == to_vec(l3));
    auto r3 = LoopifyTmc::app(l3, empty);
    ASSERT(to_vec(r3) == to_vec(l3));
  }

  // ===== map =====
  {
    auto doubled = LoopifyTmc::map<unsigned int, unsigned int>(
        [](unsigned int x) { return x * 2; }, l3);
    auto v = to_vec(doubled);
    ASSERT(v.size() == 3);
    ASSERT(v[0] == 2 && v[1] == 4 && v[2] == 6);

    auto empty_map = LoopifyTmc::map<unsigned int, unsigned int>(
        [](unsigned int x) { return x; }, empty);
    ASSERT(to_vec(empty_map).empty());
  }

  // ===== filter =====
  {
    auto evens = LoopifyTmc::filter(
        [](unsigned int x) { return x % 2 == 0; }, l5);
    auto v = to_vec(evens);
    ASSERT(v.size() == 3); // 4, 6, 8
    ASSERT(v[0] == 4 && v[1] == 6 && v[2] == 8);

    // filter keeping all
    auto all = LoopifyTmc::filter([](unsigned int) { return true; }, l3);
    ASSERT(to_vec(all) == to_vec(l3));

    // filter keeping none
    auto none = LoopifyTmc::filter([](unsigned int) { return false; }, l3);
    ASSERT(to_vec(none).empty());
  }

  // ===== snoc =====
  {
    auto result = LoopifyTmc::snoc(l3, 99u);
    auto v = to_vec(result);
    ASSERT(v.size() == 4);
    ASSERT(v[0] == 1 && v[3] == 99);

    // snoc on empty
    auto r2 = LoopifyTmc::snoc(empty, 42u);
    auto v2 = to_vec(r2);
    ASSERT(v2.size() == 1 && v2[0] == 42);
  }

  // ===== replicate =====
  {
    auto result = LoopifyTmc::replicate(5u, 7u);
    auto v = to_vec(result);
    ASSERT(v.size() == 5);
    for (auto x : v) ASSERT(x == 7);

    auto r0 = LoopifyTmc::replicate(0u, 1u);
    ASSERT(to_vec(r0).empty());
  }

  // ===== zip_with =====
  {
    auto result = LoopifyTmc::zip_with<unsigned int, unsigned int, unsigned int>(
        [](unsigned int a, unsigned int b) { return a + b; }, l3, l5);
    auto v = to_vec(result);
    ASSERT(v.size() == 3); // min length
    ASSERT(v[0] == 5 && v[1] == 7 && v[2] == 9); // 1+4, 2+5, 3+6
  }

  // ===== prefix_sums =====
  {
    auto result = LoopifyTmc::prefix_sums(0u, l3);
    auto v = to_vec(result);
    ASSERT(v.size() == 3);
    ASSERT(v[0] == 1 && v[1] == 3 && v[2] == 6); // 1, 1+2, 1+2+3
  }

  // ===== stutter =====
  {
    auto result = LoopifyTmc::stutter(l3);
    auto v = to_vec(result);
    ASSERT(v.size() == 6);
    ASSERT(v[0] == 1 && v[1] == 1 && v[2] == 2);
    ASSERT(v[3] == 2 && v[4] == 3 && v[5] == 3);

    auto empty_stut = LoopifyTmc::stutter(empty);
    ASSERT(to_vec(empty_stut).empty());
  }

  // ===== Large-input test: verify no stack overflow =====
  {
    const unsigned int N = 2000;
    auto big = List::nil();
    for (unsigned int i = 0; i < N; ++i) {
      big = List::cons(i, std::move(big));
    }

    // app on large lists
    auto appended = LoopifyTmc::app(big, List::cons(999u, List::nil()));
    ASSERT(!to_vec(appended).empty());

    // map on large list
    auto mapped = LoopifyTmc::map<unsigned int, unsigned int>(
        [](unsigned int x) { return x + 1; }, big);
    ASSERT(!to_vec(mapped).empty());

    // filter on large list (keep ~half)
    auto filtered = LoopifyTmc::filter(
        [](unsigned int x) { return x % 2 == 0; }, big);
    ASSERT(!to_vec(filtered).empty());

    // snoc on large list
    auto snocced = LoopifyTmc::snoc(big, 42u);
    ASSERT(!to_vec(snocced).empty());

    // replicate large
    auto repl = LoopifyTmc::replicate(N, 1u);
    ASSERT(!to_vec(repl).empty());

    // stutter large
    auto stuttered = LoopifyTmc::stutter(big);
    ASSERT(!to_vec(stuttered).empty());
  }

  if (testStatus == 0) {
    std::cout << "All TMC loopify tests passed!" << std::endl;
  }
  return testStatus;
}
