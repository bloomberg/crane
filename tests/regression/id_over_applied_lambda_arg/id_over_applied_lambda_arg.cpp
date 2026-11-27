#include "id_over_applied_lambda_arg.h"

uint64_t IdOverAppliedLambdaArg::one_arg(uint64_t k) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto erased_fn = crane::immortal(
      crane_erase_fn([](uint64_t n) { return (n + UINT64_C(1)); }));
  return crane::any_cast<uint64_t>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
          Datatypes::id(crane_erase_fn(
              [=](const crane::fn<uint64_t(uint64_t)> &c) { return c(k); })))(
          crane::obj(erased_fn)));
}

uint64_t IdOverAppliedLambdaArg::two_args(uint64_t k) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto erased_fn =
      crane::immortal(crane_erase_fn([](uint64_t n) { return n; }));
  static const auto id_1 = crane::immortal(Datatypes::id(
      crane_erase_fn([](const crane::fn<uint64_t(uint64_t)> &c,
                        uint64_t n) { return (c(n) + UINT64_C(1)); })));
  return crane::any_cast<uint64_t>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
          crane::any_cast<crane::fn<crane::obj(crane::obj)>>(id_1)(
              crane::obj(erased_fn)))(crane::obj(k)));
}

uint64_t IdOverAppliedLambdaArg::control(uint64_t k) {
  crane::fn<uint64_t(uint64_t)> f =
      [](uint64_t n) { return (n + UINT64_C(1)); };
  return crane::any_cast<uint64_t>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
          Datatypes::id(crane_erase_fn(
              [=](const crane::fn<uint64_t(uint64_t)> &c) { return c(k); })))(
          crane::obj(crane_erase_fn(std::move(f)))));
}

crane::obj Datatypes::id(crane::obj x) { return x; }
