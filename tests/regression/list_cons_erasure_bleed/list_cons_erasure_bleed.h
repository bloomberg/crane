#ifndef INCLUDED_LIST_CONS_ERASURE_BLEED
#define INCLUDED_LIST_CONS_ERASURE_BLEED

#include "crane_fn.h"
#include "obj.h"
#include <algorithm>
#include <cstdint>
#include <deque>
#include <utility>
#include <variant>

enum class Sym;
using tuple = crane::obj;
using syms_semty = tuple;
enum class Sym { A, B };
using sym_semty = uint64_t;
syms_semty concat_tuple_nil_case(const std::deque<Sym> &_x,
                                 const std::deque<Sym> &_x0, syms_semty _x1,
                                 syms_semty vs_);

template <typename F6>
syms_semty concat_tuple_rec_case(Sym, const std::deque<Sym> &xs_,
                                 const std::deque<Sym> &,
                                 const std::deque<Sym> &ys, syms_semty vs,
                                 syms_semty vs_, F6 &&f) {
  const auto &[s, t] = crane::any_cast<std::pair<crane::obj, crane::obj>>(vs);
  return std::make_pair(
      crane::obj(crane::any_cast<sym_semty>(s)),
      crane::obj(crane_call_erased(f, xs_, ys, t, std::move(vs_))));
}

syms_semty concat_tuple(const std::deque<Sym> &xs, const std::deque<Sym> &ys,
                        syms_semty vs, syms_semty vs_);
syms_semty rev_tuple_nil_case(const std::deque<Sym> &_x, syms_semty vs);

template <typename F4>
syms_semty rev_tuple_cons_case(const std::deque<Sym> &, Sym x,
                               const std::deque<Sym> &xs_, syms_semty vs,
                               F4 &&f) {
  const auto &[s, t] = crane::any_cast<std::pair<crane::obj, crane::obj>>(vs);
  return concat_tuple(
      [](auto _r) {
        std::reverse(_r.begin(), _r.end());
        return _r;
      }(xs_),
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(x, std::deque<Sym>{}),
      crane_call_erased(f, xs_, t),
      std::make_pair(crane::obj(crane::any_cast<sym_semty>(s)),
                     crane::obj(std::monostate{})));
}

syms_semty rev_tuple(const std::deque<Sym> &xs, syms_semty vs);
uint64_t check(uint64_t n);

#endif // INCLUDED_LIST_CONS_ERASURE_BLEED
