#ifndef INCLUDED_REGION_MEMBERSHIP_BOUNDS
#define INCLUDED_REGION_MEMBERSHIP_BOUNDS

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

struct RegionMembershipBounds {
  struct layout {
    unsigned int base_addr;
    unsigned int code_size;
  };

  __attribute__((pure)) static bool
  addr_in_regionb(const unsigned int addr, const std::shared_ptr<layout> &l);
  static inline const unsigned int t = []() {
    return [](void) {
      std::shared_ptr<layout> l = std::make_shared<layout>(layout{100u, 20u});
      return ([&](void) {
        if (addr_in_regionb(110u, l)) {
          return 1u;
        } else {
          return 0u;
        }
      }() +
              [&](void) {
                if (addr_in_regionb(121u, l)) {
                  return 1u;
                } else {
                  return 0u;
                }
              }());
    }();
  }();
};

#endif // INCLUDED_REGION_MEMBERSHIP_BOUNDS
