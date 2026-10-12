#include "rank2_alias_definition_as_value.h"

uint64_t Rank2AliasDefinitionAsValue::csum(
    Rank2AliasDefinitionAsValue::clist<uint64_t> l) {
  static const auto erased_fn = crane::immortal(crane_erase_fn<crane::obj>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }));
  return crane::any_cast<uint64_t>(l(erased_fn, UINT64_C(0)));
}

uint64_t
Rank2AliasDefinitionAsValue::fsum(Rank2AliasDefinitionAsValue::nfold l) {
  static const auto erased_fn = crane::immortal(crane_erase_fn<crane::obj>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }));
  return crane::any_cast<uint64_t>(l(erased_fn, UINT64_C(0)));
}

uint64_t Rank2AliasDefinitionAsValue::unbox(
    Rank2AliasDefinitionAsValue::box<uint64_t> b) {
  static const auto erased_fn =
      crane::immortal(crane_erase_fn<crane::obj>([](uint64_t x) { return x; }));
  return crane::any_cast<uint64_t>(b(erased_fn));
}
