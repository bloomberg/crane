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

struct NthDefaultStructSafe {
  struct L {
    struct SlotLeft {
      static unsigned int nth0(const unsigned int n);
    };
  };

  struct R {
    struct SlotRight {
      static unsigned int nth1(const unsigned int n);
    };
  };

  static inline const unsigned int t =
      (L::SlotLeft::nth0((0 + 1)) + R::SlotRight::nth1(((0 + 1) + 1)));
};
