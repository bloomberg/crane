#include "effect_recursive_list.h"

List<std::string> EffectRecursiveList::read_n_lines(uint64_t n) {
  if (n <= 0) {
    return List<std::string>::nil();
  } else {
    uint64_t n_ = n - 1;
    std::string line;
    std::getline(std::cin, line);
    List<std::string> rest = read_n_lines(n_);
    return List<std::string>::cons(line, rest);
  }
}

std::string EffectRecursiveList::fold_effect(const List<std::string> &xs,
                                             std::string acc) {
  if (std::holds_alternative<typename List<std::string>::Nil>(xs.v())) {
    return acc;
  } else {
    const auto &[a0, a1] = std::get<typename List<std::string>::Cons>(xs.v());
    std::cout << a0 << '\n';
    return fold_effect(*a1, acc + " "s + a0);
  }
}

uint64_t EffectRecursiveList::store_lines(std::string prefix, uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    std::string line;
    std::getline(std::cin, line);
    setenv(prefix.c_str(), line.c_str(), 1);
    uint64_t rest = store_lines(prefix, n_);
    return (rest + 1);
  }
}

List<std::optional<std::string>>
EffectRecursiveList::collect_envs(const List<std::string> &names) {
  if (std::holds_alternative<typename List<std::string>::Nil>(names.v())) {
    return List<std::optional<std::string>>::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::string>::Cons>(names.v());
    std::optional<std::string> val = [&]() -> std::optional<std::string> {
      auto *v = std::getenv(a0.c_str());
      return v ? std::optional<std::string>(v) : std::optional<std::string>();
    }();
    List<std::optional<std::string>> vals = collect_envs(*a1);
    return List<std::optional<std::string>>::cons(val, vals);
  }
}

List<std::string> EffectRecursiveList::read_and_prepend(List<std::string> xs) {
  std::string line;
  std::getline(std::cin, line);
  return List<std::string>::cons(line, xs);
}
