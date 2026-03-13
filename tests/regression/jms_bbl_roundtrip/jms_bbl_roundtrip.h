#ifndef INCLUDED_JMS_BBL_ROUNDTRIP
#define INCLUDED_JMS_BBL_ROUNDTRIP

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

struct JmsBblRoundtrip {
  struct state {
    unsigned int pc;
    unsigned int ret;
    bool has_ret;
  };

  __attribute__((pure)) static unsigned int addr12_of_nat(const unsigned int n);
  static std::shared_ptr<state> execute_jms(std::shared_ptr<state> s,
                                            const unsigned int addr);
  static std::shared_ptr<state> execute_bbl(std::shared_ptr<state> s);
  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{100u, 0u, false});
  static inline const bool t =
      execute_bbl(execute_jms(sample, 200u))->pc == 102u;
};

#endif // INCLUDED_JMS_BBL_ROUNDTRIP
