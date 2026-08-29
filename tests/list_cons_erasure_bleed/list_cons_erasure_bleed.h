#ifndef INCLUDED_LIST_CONS_ERASURE_BLEED
#define INCLUDED_LIST_CONS_ERASURE_BLEED

#include "crane_fn.h"
#include <algorithm>
#include <any>
#include <deque>
#include <type_traits>
#include <utility>
#include <variant>

using tuple = std::any;
enum class Sym { A, B };
using sym_semty = uint64_t;
using syms_semty = tuple;
syms_semty concat_tuple_nil_case(const std::deque<Sym> &_x,
                                 const std::deque<Sym> &_x0, syms_semty _x1,
                                 syms_semty vs_);

template <typename F6>
  requires std::is_invocable_r_v<syms_semty, F6 &, std::deque<Sym> &,
                                 std::deque<Sym> &, syms_semty &, syms_semty &>
syms_semty concat_tuple_rec_case(Sym, const std::deque<Sym> &xs_,
                                 const std::deque<Sym> &,
                                 const std::deque<Sym> &ys, syms_semty vs,
                                 syms_semty vs_, F6 &&f) {
  const auto &[s, t] = std::any_cast<std::pair<std::any, std::any>>(vs);
  return std::make_pair(std::any(std::any_cast<sym_semty>(s)),
                        std::any(crane_call_erased(f, xs_, ys, t, vs_)));
}

syms_semty concat_tuple(const std::deque<Sym> &xs, const std::deque<Sym> &ys,
                        syms_semty vs, syms_semty vs_);
syms_semty rev_tuple_nil_case(const std::deque<Sym> &_x, syms_semty vs);

template <typename F4>
  requires std::is_invocable_r_v<syms_semty, F4 &, std::deque<Sym> &,
                                 syms_semty &>
syms_semty rev_tuple_cons_case(const std::deque<Sym> &, Sym x,
                               const std::deque<Sym> &xs_, syms_semty vs,
                               F4 &&f) {
  const auto &[s, t] = std::any_cast<std::pair<std::any, std::any>>(vs);
  return concat_tuple(
      [&]() {
        auto _r = xs_;
        std::reverse(_r.begin(), _r.end());
        return _r;
      }(),
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(x, std::deque<Sym>{}),
      crane_call_erased(f, xs_, t),
      std::make_pair(std::any(std::any_cast<sym_semty>(s)),
                     std::any(std::monostate{})));
}

syms_semty rev_tuple(const std::deque<Sym> &xs, syms_semty vs);

template <typename T1> std::deque<std::any> _check_map(const std::deque<T1> l) {
  if (l.empty()) {
    return std::deque<std::any>{};
  } else {
    const auto &a = l.front();
    std::decay_t<decltype(l)> l0(l.begin() + 1, l.end());
    return [](auto _a0, auto _a1) {
      _a1.push_front(_a0);
      return _a1;
    }(std::any(), _check_map<T1>(l0));
  }
}

uint64_t check(uint64_t n);

#endif // INCLUDED_LIST_CONS_ERASURE_BLEED
