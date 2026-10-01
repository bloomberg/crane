#include "instance_in_collision_wrapper_named_bare.h"
#include <cassert>
#include <cstdio>

namespace {

Nat nat(unsigned n) {
  Nat acc = Nat::o();
  for (unsigned i = 0; i < n; ++i) acc = Nat::s(std::move(acc));
  return acc;
}

unsigned to_unsigned(const Nat &n) {
  unsigned c = 0;
  const Nat *cur = &n;
  while (std::holds_alternative<Nat::S>(cur->v())) {
    cur = std::get<Nat::S>(cur->v()).a0.get();
    ++c;
  }
  return c;
}

}  // namespace

int main() {
  using Tbl = List<std::pair<AstLike::Raw_id, Nat>>;
  const Tbl table = Tbl::cons({AstLike::Raw_id::name(nat(2)), nat(7)},
                              Tbl::cons({AstLike::Raw_id::anon(nat(3)), nat(9)},
                                        Tbl::nil()));

  // [assoc] names the instance implicitly; [describe] names the same file
  // explicitly and is the control.
  const auto hit = both(AstLike::Raw_id::name(nat(2)), table);
  assert(std::holds_alternative<Ident::Global>(hit.first.v()));
  assert(to_unsigned(hit.second.first) == 2);
  assert(hit.second.second.has_value());
  assert(to_unsigned(*hit.second.second) == 7);

  const auto miss = both(AstLike::Raw_id::name(nat(5)), table);
  assert(!miss.second.second.has_value());

  // Instance and control side by side in one statement.
  const auto one = both_at_one_site(AstLike::Raw_id::anon(nat(3)), table);
  assert(to_unsigned(one.first) == 4);
  assert(one.second.has_value());
  assert(to_unsigned(*one.second) == 9);

  printf("All instance_in_collision_wrapper_named_bare tests passed!\n");
  return 0;
}
