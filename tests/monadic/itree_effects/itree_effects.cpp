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
    [](uint64_t _crane_n, auto _crane_f, auto _crane_seed) {
      std::decay_t<decltype(_crane_f(std::move(_crane_seed)))> _crane_acc =
          std::move(_crane_seed);
      for (uint64_t _crane_i = 0; _crane_i < _crane_n; _crane_i++) {
        _crane_acc = _crane_f(std::move(_crane_acc));
      }
      return _crane_acc;
    }(
        n,
        [](const auto &acc) {
          std::string line;
          std::getline(std::cin, line);
          std::cout << line << '\n';
          return acc;
        },
        std::monostate{});
    return;
  }
}
