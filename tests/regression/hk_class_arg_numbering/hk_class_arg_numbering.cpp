#include "hk_class_arg_numbering.h"

std::optional<Nat> HkClassArgNumbering::use(const Nat &n) {
  return run<Iter_option, Functor_Monad<Monad_option>, Monad_option, Nat>(
      [](const Nat &m) { return std::make_optional<Nat>(Nat::s(m)); }, n);
}
