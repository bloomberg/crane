#include "name_prefixed_by_file.h"

EOU<Nat> NamePrefixedByFile::use(const Nat &n) {
  return EOU_monad::template bind<Nat, Nat>(
      EOU0::template option_ub<Nat>(Nat::o(), std::make_optional<Nat>(n)),
      [](const Nat &x) { return EOU_monad::template ret<Nat>(Nat::s(x)); });
}
