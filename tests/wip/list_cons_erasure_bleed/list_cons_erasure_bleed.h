#ifndef INCLUDED_LIST_CONS_ERASURE_BLEED
#define INCLUDED_LIST_CONS_ERASURE_BLEED

#include "crane_fn.h"
#include <algorithm>
#include <any>
#include <deque>
#include <type_traits>
#include <utility>
#include <variant>

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

/// Compile-time repro. After Defs.v's rev_tuple_cons_case singleton-tuple
/// erasure bug was fixed (previous wip: erased_singleton_unit_tuple), the
/// generated code for rev_tuple_cons_case now correctly emits a properly
/// erased pair<any,any> for the value tuple -- but a NEW bug appeared in
/// the SAME function: it also builds the CONCRETE singleton grammar-symbol
/// list x (a plain list symbol, NOT an erased symbols_semty value),
/// and this now ALSO gets erased/mis-typed, e.g. (observed in
/// benchmarking/crane_extracted/Benchmarking/Defs.h):
///
/// (auto _a0, auto _a1) { _a1.push_front(_a0); return _a1; }(
/// std::any(std::move(x)), std::deque<Symbol>{})
///
/// where _a1 is std::deque<Symbol>, so push_front requires a concrete
/// Symbol, not std::any -- "no matching member function for call to
/// 'push_front'".
///
/// This file mirrors theories/Parser/Defs.v's concat_tuple/rev_tuple
/// family verbatim (same tactic-built dependent-case-split style, same
/// symbols_semty gamma := tuple (map symbol_semty gamma) domain), with
/// sym standing in for symbol. rev_tuple_cons_case calls
/// concat_tuple (rev xs') [x] (f xs' vs) (v, tt) -- exactly like the real
/// one -- where [x] : list sym is a concrete singleton grammar-symbol list
/// built in the SAME function that also builds the erased singleton value
/// tuple (v, tt) : syms_semty [x]. check forces rev_tuple on a
/// two-element list so Crane must extract rev_tuple_cons_case for real.
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
      }(std::any(x), std::deque<Sym>{}),
      crane_call_erased(f, xs_, t),
      std::make_pair(std::any_cast<sym_semty>(s), std::any(std::monostate{})));
}

syms_semty rev_tuple(const std::deque<Sym> &xs, syms_semty vs);
uint64_t check(uint64_t n);

#endif // INCLUDED_LIST_CONS_ERASURE_BLEED
