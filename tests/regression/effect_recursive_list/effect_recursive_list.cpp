#include <effect_recursive_list.h>

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// 1. Recursive function building a list from stdin lines
List<std::string> EffectRecursiveList::read_n_lines(const unsigned int &n) {
  if (n <= 0) {
    return List<std::string>::nil();
  } else {
    unsigned int n_ = n - 1;
    std::string line;
    std::getline(std::cin, line);
    List<std::string> rest = read_n_lines(n_);
    return List<std::string>::cons(line, rest);
  }
}

/// 3. Fold a list with effects, accumulating a result
std::string EffectRecursiveList::fold_effect(const List<std::string> &xs,
                                             const std::string acc) {
  if (std::holds_alternative<typename List<std::string>::Nil>(xs.v())) {
    return acc;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<std::string>::Cons>(xs.v());
    std::cout << d_a0 << '\n';
    return fold_effect(*(d_a1), acc + " "s + d_a0);
  }
}

/// 4. Read lines and store each in env with index
unsigned int EffectRecursiveList::store_lines(const std::string prefix,
                                              const unsigned int &n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    std::string line;
    std::getline(std::cin, line);
    setenv(prefix.c_str(), line.c_str(), 1);
    unsigned int rest = store_lines(prefix, n_);
    return (rest + 1);
  }
}

/// 5. Collect env values into a list
List<std::optional<std::string>>
EffectRecursiveList::collect_envs(const List<std::string> &names) {
  if (std::holds_alternative<typename List<std::string>::Nil>(names.v())) {
    return List<std::optional<std::string>>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<std::string>::Cons>(names.v());
    std::optional<std::string> val = [&]() -> std::optional<std::string> {
      auto *v = std::getenv(d_a0.c_str());
      return v ? std::optional<std::string>(v) : std::optional<std::string>();
    }();
    List<std::optional<std::string>> vals = collect_envs(*(d_a1));
    return List<std::optional<std::string>>::cons(val, vals);
  }
}

/// 6. Read a line and prepend to existing list
List<std::string> EffectRecursiveList::read_and_prepend(List<std::string> xs) {
  std::string line;
  std::getline(std::cin, line);
  return List<std::string>::cons(line, xs);
}
