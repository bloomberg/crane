#include "hk_class_arg_numbering.h"

std::optional<Nat> HkClassArgNumbering::use(const Nat &n) {
  return run<Functor_Monad<Monad_option>, Monad_option, Nat>(
      [](std::function<std::optional<std::any>(std::any)> _ec0, std::any _ec1) {
        return Iter_option(_ec0, _ec1);
      },
      [](Nat m) { return std::make_optional<Nat>(Nat::s(m)); }, n);
}
