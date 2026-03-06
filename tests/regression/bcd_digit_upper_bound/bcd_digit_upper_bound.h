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

struct BcdDigitUpperBound {
  static bool is_bcd_digitb(const unsigned int n);

  static inline const unsigned int t =
      ([](void) {
        if (is_bcd_digitb((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1))) {
          return (0 + 1);
        } else {
          return 0;
        }
      }() +
       [](void) {
         if (is_bcd_digitb(
                 ((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                    1) +
                   1) +
                  1))) {
           return (0 + 1);
         } else {
           return 0;
         }
       }());
};
