#include "void_callback.h"

void VoidCallback::print_nat(uint64_t) { return; }

void VoidCallback::test_for_each_m() {
  for_each_m(
      [](uint64_t) {
        std::cout << "item"s << '\n';
        return std::monostate{};
      },
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())));
  return;
}

/// 3. Pure function returning unit, used in let
void VoidCallback::side_effect_pure(uint64_t) { return; }

/// 7. Void returning function in a match arm
void VoidCallback::void_in_match(bool b) {
  if (b) {
    print_nat(UINT64_C(1));
    return;
  } else {
    print_nat(UINT64_C(2));
    return;
  }
}

/// 8. Option of void function result
std::optional<std::monostate> VoidCallback::void_option(bool b) {
  if (b) {
    return std::make_optional<std::monostate>([]() {
      print_nat(UINT64_C(1));
      return std::monostate{};
    }());
  } else {
    return std::optional<std::monostate>();
  }
}
