#include "erased_singleton_unit_tuple.h"

syms_semty cons_sem(Sym, const List<Sym> &, sym_semty v, syms_semty rest) {
  return std::make_pair(crane::obj(v), crane::obj(rest));
}

syms_semty head1(const List<Sym> &, syms_semty vs) {
  const auto &[v, _x0] = crane::any_cast<std::pair<crane::obj, crane::obj>>(vs);
  return std::make_pair(crane::obj(v), crane::obj(std::monostate{}));
}

uint64_t firstOf(const List<Sym> &, syms_semty t) {
  const auto &[v, _x0] = crane::any_cast<std::pair<crane::obj, crane::obj>>(t);
  return crane::any_cast<uint64_t>(v);
}

uint64_t check(uint64_t n) {
  return firstOf(
      List<Sym>::nil(),
      head1(List<Sym>::cons(Sym::B, List<Sym>::nil()),
            cons_sem(Sym::A, List<Sym>::cons(Sym::B, List<Sym>::nil()), n,
                     cons_sem(Sym::B, List<Sym>::nil(), n, std::monostate{}))));
}
