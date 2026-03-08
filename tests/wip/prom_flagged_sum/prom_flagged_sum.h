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

struct PromFlaggedSum {
  struct state {
    unsigned int acc;
    unsigned int prom_addr;
    unsigned int prom_data;
    bool prom_enable;
  };

  static unsigned int flagged_sum(const std::shared_ptr<state> &s);

  static inline const unsigned int t =
      flagged_sum(std::make_shared<state>(state{3u, 12u, 77u, false}));
};
