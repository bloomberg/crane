#include "id_fn_result_unboxed.h"

IdFnResultUnboxed::stream IdFnResultUnboxed::sconst(uint64_t n) {
  return stream::lazy_(
      [=]() mutable -> typename IdFnResultUnboxed::stream::SCons {
        return {n, sconst(n)};
      });
}

uint64_t IdFnResultUnboxed::len(const List<uint64_t> &x0_) {
  return x0_.length();
}

List<uint64_t> IdFnResultUnboxed::dup(uint64_t n) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto id_1 =
      crane::immortal(Datatypes::id(crane_erase_fn([](uint64_t k) {
        return List<crane::obj>::cons(
            k, List<crane::obj>::cons(k, List<crane::obj>::nil()));
      })));
  return List<uint64_t>(crane::any_cast<List<crane::obj>>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(id_1)(crane::obj(n))));
}

uint64_t IdFnResultUnboxed::head_or_7(uint64_t n) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto id_1 =
      crane::immortal(Datatypes::id(crane_erase_fn([](uint64_t k) {
        return List<crane::obj>::cons(k, List<crane::obj>::nil());
      })));
  auto &&_sv = List<uint64_t>(crane::any_cast<List<crane::obj>>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(id_1)(crane::obj(n))));
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return UINT64_C(7);
  } else {
    const auto &[a0, _] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    return a0;
  }
}

crane::obj Datatypes::id(crane::obj x) { return x; }
