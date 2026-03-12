#ifndef INCLUDED_KBP_MULTIBIT_DEFAULT
#define INCLUDED_KBP_MULTIBIT_DEFAULT

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct KbpMultibitDefault {
  struct state {
    unsigned int acc;
  };

  static std::shared_ptr<state> execute_kbp(const std::shared_ptr<state> &s);
  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{3u});

  static inline const bool t = (execute_kbp(sample)->acc == 15u);
};

#endif // INCLUDED_KBP_MULTIBIT_DEFAULT
