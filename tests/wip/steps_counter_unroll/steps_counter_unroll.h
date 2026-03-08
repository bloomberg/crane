#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct StepsCounterUnroll {
  struct state {
    unsigned int pc;
  };

  static std::shared_ptr<state> step(std::shared_ptr<state> s);

  static std::shared_ptr<state> steps(const unsigned int n,
                                      std::shared_ptr<state> s);

  static inline const unsigned int t =
      steps(5u, std::make_shared<state>(state{4094u}))->pc;
};
