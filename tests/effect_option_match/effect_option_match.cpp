#include "effect_option_match.h"

std::string EffectOptionMatch::show_or_default(std::string name,
                                               std::string default0) {
  std::optional<std::string> mv = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (mv.has_value()) {
    const std::string &v = *mv;
    return v;
  } else {
    return default0;
  }
}

std::string EffectOptionMatch::show_or_ask(std::string name) {
  std::optional<std::string> mv = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (mv.has_value()) {
    const std::string &v = *mv;
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

std::string EffectOptionMatch::get_first_set(const List<std::string> &names) {
  if (std::holds_alternative<typename List<std::string>::Nil>(names.v())) {
    return "none";
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::string>::Cons>(names.v());
    std::optional<std::string> mv = [&]() -> std::optional<std::string> {
      auto *v = std::getenv(a0.c_str());
      return v ? std::optional<std::string>(v) : std::optional<std::string>();
    }();
    if (mv.has_value()) {
      const std::string &v = *mv;
      return v;
    } else {
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<std::string>::Nil>(_sv0.v())) {
        return "none";
      } else {
        const auto &[a00, a10] =
            std::get<typename List<std::string>::Cons>(_sv0.v());
        std::optional<std::string> mv2 = [&]() -> std::optional<std::string> {
          auto *v = std::getenv(a00.c_str());
          return v ? std::optional<std::string>(v)
                   : std::optional<std::string>();
        }();
        if (mv2.has_value()) {
          const std::string &v2 = *mv2;
          return v2;
        } else {
          return "none";
        }
      }
    }
  }
}

bool EffectOptionMatch::set_and_verify(std::string name, std::string value) {
  setenv(name.c_str(), value.c_str(), 1);
  std::optional<std::string> mv = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (mv.has_value()) {
    const std::string &_x0 = *mv;
    return true;
  } else {
    return false;
  }
}

std::optional<std::string>
EffectOptionMatch::find_env_value(const List<std::string> &names) {
  if (std::holds_alternative<typename List<std::string>::Nil>(names.v())) {
    return std::optional<std::string>();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::string>::Cons>(names.v());
    std::optional<std::string> mv = [&]() -> std::optional<std::string> {
      auto *v = std::getenv(a0.c_str());
      return v ? std::optional<std::string>(v) : std::optional<std::string>();
    }();
    if (mv.has_value()) {
      const std::string &v = *mv;
      return std::make_optional<std::string>(v);
    } else {
      return find_env_value(*a1);
    }
  }
}
