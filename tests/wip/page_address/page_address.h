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

struct PageAddress {
  static unsigned int addr12_of_nat(const unsigned int n);

  static unsigned int page_of(const unsigned int p);

  static unsigned int page_base(const unsigned int p);

  static unsigned int branch_target(const unsigned int pc,
                                    const unsigned int off);

  static inline const unsigned int p_small = 777u;

  static inline const unsigned int p_same = 600u;

  static inline const unsigned int p_cross_254 = 254u;

  static inline const unsigned int p_cross_255 = 255u;

  static inline const unsigned int page_base_777 = page_base(777u);

  static inline const unsigned int branch_example = branch_target(100u, 42u);
};
