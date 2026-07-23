#include "list_cons_erasure_bleed.h"

syms_semty concat_tuple_nil_case(const std::deque<Sym> &,
                                 const std::deque<Sym> &, syms_semty,
                                 syms_semty vs_) {
  return vs_;
}

syms_semty concat_tuple(const std::deque<Sym> &xs, const std::deque<Sym> &ys,
                        syms_semty vs, syms_semty vs_) {
  if (xs.empty()) {
    return concat_tuple_nil_case(xs, ys, vs, vs_);
  } else {
    const auto &x = xs.front();
    std::decay_t<decltype(xs)> xs_(xs.begin() + 1, xs.end());
    return concat_tuple_rec_case(x, xs_, xs, ys, vs, vs_, concat_tuple);
  }
}

syms_semty rev_tuple_nil_case(const std::deque<Sym> &, syms_semty vs) {
  return vs;
}

syms_semty rev_tuple(const std::deque<Sym> &xs, syms_semty vs) {
  if (xs.empty()) {
    return rev_tuple_nil_case(xs, vs);
  } else {
    const auto &x = xs.front();
    std::decay_t<decltype(xs)> xs_(xs.begin() + 1, xs.end());
    return rev_tuple_cons_case(xs, x, xs_, vs, rev_tuple);
  }
}

uint64_t check(uint64_t n) {
  auto [v, _x] = rev_tuple(
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(Sym::A,
        [](auto _a0, auto _a1) {
          _a1.push_front(_a0);
          return _a1;
        }(Sym::B, std::deque<Sym>{})),
      std::make_pair(n, std::make_pair(n, std::monostate{})));
  return v;
}
