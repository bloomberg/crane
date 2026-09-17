#include "member_alias_as_tt_arg.h"

std::optional<std::pair<Nat, Nat>> MemberAliasAsTtArg::use(const Nat &o) {
  return run<Monad_option, Nat>(
      [](Nat s) {
        return std::make_optional<std::pair<Nat, Nat>>(
            std::make_pair(Nat::s(s), s));
      },
      o);
}
