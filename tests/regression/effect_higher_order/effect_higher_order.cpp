#include <effect_higher_order.h>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// 5. Effectful callback passed as argument
void EffectHigherOrder::greet_all(
    const std::shared_ptr<List<std::string>> &names) {
  for_each_str(
      [](const std::string name) {
        std::cout << "Hello, "s + name << '\n';
        return std::monostate{};
      },
      names);
  return;
}

/// 6. Callback with env effect
std::string EffectHigherOrder::lookup_or_ask(const std::string name) {
  std::optional<std::string> mv = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (mv.has_value()) {
    const std::string &v = *mv;
    return v;
  } else {
    std::cout << "Enter "s + name + ":"s << '\n';
    std::string line;
    std::getline(std::cin, line);
    setenv(name.c_str(), line.c_str(), 1);
    return line;
  }
}

/// 7. Chain of lookups
std::shared_ptr<List<std::string>>
EffectHigherOrder::lookup_all(const std::shared_ptr<List<std::string>> &names) {
  if (std::holds_alternative<typename List<std::string>::Nil>(names->v())) {
    return List<std::string>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<std::string>::Cons>(names->v());
    std::string v = lookup_or_ask(d_a0);
    std::shared_ptr<List<std::string>> vs = lookup_all(d_a1);
    return List<std::string>::cons(v, vs);
  }
}

/// 8. Effect in let-bound function
std::string EffectHigherOrder::process_input() {
  std::function<std::string(std::string)> format = [](const std::string s) {
    return "["s + s + "]"s;
  };
  std::string line;
  std::getline(std::cin, line);
  return format(line);
}
