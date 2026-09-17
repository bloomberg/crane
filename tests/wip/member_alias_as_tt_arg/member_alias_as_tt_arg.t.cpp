#include <member_alias_as_tt_arg.h>

#include <cassert>

int main() {
  // (fun s => Some (S s, s)) at 3 gives Some (4, 3).
  auto r = MemberAliasAsTtArg::use(Nat::s(Nat::s(Nat::s(Nat::o()))));
  assert(r.has_value());
  return 0;
}
