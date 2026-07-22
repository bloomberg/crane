#include "itree_effects.h"

/// ------------------------------------------------------------------
void ITreeEffects::greet() {
  std::cout << "What is your name?"s << '\n';
  std::string name;
  std::getline(std::cin, name);
  std::cout << name << '\n';
  return;
}

uint64_t ITreeEffects::roll_dice(uint64_t sides) {
  uint64_t n = (std::rand() % sides);
  return (n + UINT64_C(1));
}

void ITreeEffects::timed_greeting() {
  uint64_t t = static_cast<unsigned int>(std::time(nullptr));
  std::cout << [&]() -> std::string {
    if (t <= UINT64_C(43200)) {
      return "Good morning";
    } else {
      return "Good afternoon";
    }
  }() << '\n';
  return;
}

void ITreeEffects::echo_loop(uint64_t n) {
  {
    [&]() {
      auto _acc = std::monostate{};
      for (uint64_t _i = 0; _i < n; _i++) {
        _acc = [](const auto &acc) {
          std::string line;
          std::getline(std::cin, line);
          std::cout << line << '\n';
          return acc;
        }(std::move(_acc));
      }
      return _acc;
    }();
    return;
  }
}
