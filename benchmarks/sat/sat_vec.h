// Reference-semantics growable vector backing the [vecE] effect.
//
// With SATBENCH_CHECKED defined, every operation checks the precondition its
// [step] rule in VecSem.v has (index < length for get/set, n <= length for
// shrink) and aborts if it fails. The default build is unchecked.
#pragma once
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <stdexcept>
#include <variant>
#include <vector>

namespace satbench {
#ifdef SATBENCH_CHECKED
inline void check(bool ok, const char *what, uint64_t i, uint64_t len) {
  if (ok) return;
  std::fprintf(stderr, "satbench::vec: %s %llu out of bounds (length %llu)\n",
               what, (unsigned long long)i, (unsigned long long)len);
  std::abort();
}
#define SATBENCH_CHECK(ok, what, i) check(ok, what, i, p->size())
#else
#define SATBENCH_CHECK(ok, what, i) ((void)0)
#endif

template <class T> struct vec {
  std::shared_ptr<std::vector<T>> p;
  static vec make(uint64_t n, T x) {
    return vec{std::make_shared<std::vector<T>>(n, std::move(x))};
  }
  T get(uint64_t i) const {
    SATBENCH_CHECK(i < p->size(), "get", i);
    return (*p)[i];
  }
  std::monostate set(uint64_t i, T x) const {
    SATBENCH_CHECK(i < p->size(), "set", i);
    (*p)[i] = std::move(x);
    return {};
  }
  uint64_t len() const { return p->size(); }
  std::monostate push(T x) const { p->push_back(std::move(x)); return {}; }
  std::monostate shrink(uint64_t n) const {
    SATBENCH_CHECK(n <= p->size(), "shrink", n);
    p->resize(n);
    return {};
  }
};

// A loop ran out of fuel (see [VAbort]); [site] says which.
struct out_of_fuel : std::runtime_error {
  uint64_t site;
  explicit out_of_fuel(uint64_t s) : std::runtime_error("out of fuel"), site(s) {}
};
template <class T> [[noreturn]] T abort(uint64_t site) { throw out_of_fuel(site); }

template <class T> vec<T> make_vec(uint64_t n, T x) {
  return vec<T>::make(n, std::move(x));
}
} // namespace satbench
