#include "name_prefixed_by_file.h"

EOU<Nat> NamePrefixedByFile::use(Nat n) {
  return Monad0::template bind<EOU_monad, Nat, Nat>(
      EOU0::template option_ub<Nat>(Nat::o(),
                                    std::make_optional<Nat>(std::move(n))),
      [](Nat x) { return Monad0::template ret<EOU_monad, Nat>(Nat::s(x)); });
}
