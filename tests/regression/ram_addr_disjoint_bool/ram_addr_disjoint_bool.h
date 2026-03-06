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

struct RamAddrDisjointBool {
  static bool ram_addr_disjointb(const unsigned int b1, const unsigned int c1,
                                 const unsigned int r1, const unsigned int i1,
                                 const unsigned int b2, const unsigned int c2,
                                 const unsigned int r2, const unsigned int i2);

  static inline const unsigned int t =
      ([](void) {
        if (ram_addr_disjointb(0, (0 + 1), ((0 + 1) + 1), (((0 + 1) + 1) + 1),
                               0, (0 + 1), ((0 + 1) + 1),
                               (((0 + 1) + 1) + 1))) {
          return (0 + 1);
        } else {
          return 0;
        }
      }() +
       [](void) {
         if (ram_addr_disjointb(0, (0 + 1), ((0 + 1) + 1), (((0 + 1) + 1) + 1),
                                0, (0 + 1), ((0 + 1) + 1),
                                ((((0 + 1) + 1) + 1) + 1))) {
           return (0 + 1);
         } else {
           return 0;
         }
       }());
};
