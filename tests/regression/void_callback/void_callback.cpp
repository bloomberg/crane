#include <void_callback.h>

void VoidCallback::print_nat(const unsigned int &) { return; }

void VoidCallback::test_for_each_m() {
  for_each_m(
      [](const unsigned int &) {
        std::cout << "item"s << '\n';
        return std::monostate{};
      },
      List<unsigned int>::cons(
          1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())));
  return;
}

/// 3. Pure function returning unit, used in let
void VoidCallback::side_effect_pure(const unsigned int &) { return; }

/// 7. Void returning function in a match arm
void VoidCallback::void_in_match(const bool &b) {
  if (b) {
    print_nat(1u);
    return;
  } else {
    print_nat(2u);
    return;
  }
}

/// 8. Option of void function result
__attribute__((pure)) std::optional<std::monostate>
VoidCallback::void_option(const bool &b) {
  if (b) {
    return std::make_optional<std::monostate>([]() {
      print_nat(1u);
      return std::monostate{};
    }());
  } else {
    return std::optional<std::monostate>();
  }
}
