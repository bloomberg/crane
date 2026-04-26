#include <effect_cross_module.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// Inner module defines a helper that returns a value
void EffectCrossModule::Inner::greet(const std::string name) {
  std::cout << "Hello, "s + name << '\n';
  return;
}

std::string EffectCrossModule::Inner::ask_name() {
  std::cout << "What is your name?"s << '\n';
  return []() -> std::string {
    std::string _r;
    std::getline(std::cin, _r);
    return _r;
  }();
}

/// Outer code uses Inner's definitions
void EffectCrossModule::test_greet() {
  Inner::greet("world");
  return;
}

std::string EffectCrossModule::test_ask_name() { return Inner::ask_name(); }

int64_t EffectCrossModule::test_with_greeting() {
  return Inner::template with_greeting<int64_t>(
      [](const std::string name) { return name.length(); });
}

/// Use Inner's helper in a recursive function
void EffectCrossModule::greet_all(const List<std::string> &names) {
  if (std::holds_alternative<typename List<std::string>::Nil>(names.v())) {
    return;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<std::string>::Cons>(names.v());
    Inner::greet(d_a0);
    greet_all(*(d_a1));
    return;
  }
}

/// Use two effects from different modules
std::string EffectCrossModule::combined_io_op() {
  std::string name = Inner::ask_name();
  [&]() {
    std::ofstream file("last_name.txt"s);
    file << name;
  }();
  return name;
}
