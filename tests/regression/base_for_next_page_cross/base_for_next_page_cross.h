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

struct Nat {
  static std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                                      const unsigned int y,
                                                      const unsigned int q,
                                                      const unsigned int u);

  static unsigned int div(const unsigned int x, const unsigned int y);
};

struct BaseForNextPageCross {
  struct state {
    unsigned int pc;
  };

  static unsigned int addr12_of_nat(const unsigned int n);

  static unsigned int pc_inc1(const std::shared_ptr<state> &s);

  static unsigned int pc_inc2(const std::shared_ptr<state> &s);

  static unsigned int page_of(const unsigned int p);

  static unsigned int page_base(const unsigned int p);

  static unsigned int base_for_next1(const std::shared_ptr<state> &s);

  static unsigned int base_for_next2(const std::shared_ptr<state> &s);

  static inline const unsigned int test_next1 =
      base_for_next1(std::make_shared<state>(state{255u}));

  static inline const unsigned int test_next2 =
      base_for_next2(std::make_shared<state>(state{255u}));

  static inline const std::pair<unsigned int, unsigned int> t =
      std::make_pair(test_next1, test_next2);
};
