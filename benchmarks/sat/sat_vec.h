// Reference-semantics growable vector backing the [vecE] effect.
#pragma once
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <variant>
#include <vector>

namespace satbench {
template <class T> struct vec {
  std::shared_ptr<std::vector<T>> p;
  static vec make(uint64_t n, T x) {
    return vec{std::make_shared<std::vector<T>>(n, std::move(x))};
  }
  T get(uint64_t i) const { return (*p)[i]; }
  std::monostate set(uint64_t i, T x) const { (*p)[i] = std::move(x); return {}; }
  uint64_t len() const { return p->size(); }
  std::monostate push(T x) const { p->push_back(std::move(x)); return {}; }
  std::monostate shrink(uint64_t n) const { p->resize(n); return {}; }
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
