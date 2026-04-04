#include <effect_option_match.h>

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// 1. get_env returns option, match immediately
std::string EffectOptionMatch::show_or_default(const std::string name,
                                               const std::string default0) {
  std::optional<std::string> mv = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (mv.has_value()) {
    std::string v = *mv;
    return v;
  } else {
    return default0;
  }
}

/// 2. get_env with effect in one branch
std::string EffectOptionMatch::show_or_ask(const std::string name) {
  std::optional<std::string> mv = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (mv.has_value()) {
    std::string v = *mv;
    return v;
  } else {
    std::cout << "Not set, enter value:"s << '\n';
    return []() -> std::string {
      std::string _r;
      std::getline(std::cin, _r);
      return _r;
    }();
  }
}

/// 3. Multiple option matches in sequence
std::string EffectOptionMatch::get_first_set(
    const std::shared_ptr<List<std::string>> &names) {
  return std::visit(
      Overloaded{
          [](const typename List<std::string>::Nil _args) -> std::string {
            return "none";
          },
          [](const typename List<std::string>::Cons _args) -> std::string {
            std::optional<std::string> mv =
                [&]() -> std::optional<std::string> {
              auto *v = std::getenv(_args.d_a0.c_str());
              return v ? std::optional<std::string>(v)
                       : std::optional<std::string>();
            }();
            if (mv.has_value()) {
              std::string v = *mv;
              return v;
            } else {
              return std::visit(
                  Overloaded{[](const typename List<std::string>::Nil _args0)
                                 -> std::string { return "none"; },
                             [](const typename List<std::string>::Cons _args0)
                                 -> std::string {
                               std::optional<std::string> mv2 =
                                   [&]() -> std::optional<std::string> {
                                 auto *v = std::getenv(_args0.d_a0.c_str());
                                 return v ? std::optional<std::string>(v)
                                          : std::optional<std::string>();
                               }();
                               if (mv2.has_value()) {
                                 std::string v2 = *mv2;
                                 return v2;
                               } else {
                                 return "none";
                               }
                             }},
                  _args.d_a1->v());
            }
          }},
      names->v());
}

/// 4. set then get, match on result
bool EffectOptionMatch::set_and_verify(const std::string name,
                                       const std::string value) {
  setenv(name.c_str(), value.c_str(), 1);
  std::optional<std::string> mv = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (mv.has_value()) {
    std::string _x0 = *mv;
    return true;
  } else {
    return false;
  }
}

/// 5. Recursive function with option matching
std::optional<std::string> EffectOptionMatch::find_env_value(
    const std::shared_ptr<List<std::string>> &names) {
  return std::visit(Overloaded{[](const typename List<std::string>::Nil _args)
                                   -> std::optional<std::string> {
                                 return std::optional<std::string>();
                               },
                               [](const typename List<std::string>::Cons _args)
                                   -> std::optional<std::string> {
                                 std::optional<std::string> mv =
                                     [&]() -> std::optional<std::string> {
                                   auto *v = std::getenv(_args.d_a0.c_str());
                                   return v ? std::optional<std::string>(v)
                                            : std::optional<std::string>();
                                 }();
                                 if (mv.has_value()) {
                                   std::string v = *mv;
                                   return std::make_optional<std::string>(v);
                                 } else {
                                   return find_env_value(_args.d_a1);
                                 }
                               }},
                    names->v());
}
