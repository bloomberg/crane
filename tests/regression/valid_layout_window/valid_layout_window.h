#ifndef INCLUDED_VALID_LAYOUT_WINDOW
#define INCLUDED_VALID_LAYOUT_WINDOW

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

struct ValidLayoutWindow {
  struct layout {
    unsigned int base_addr;
    unsigned int code_size;
  };

  __attribute__((pure)) static bool
  valid_layoutb(const std::shared_ptr<layout> &l);
  static inline const unsigned int t =
      ([](void) {
        if (valid_layoutb(std::make_shared<layout>(layout{128u, 256u}))) {
          return 1u;
        } else {
          return 0u;
        }
      }() +
       [](void) {
         if (valid_layoutb(std::make_shared<layout>(layout{4090u, 20u}))) {
           return 1u;
         } else {
           return 0u;
         }
       }());
};

#endif // INCLUDED_VALID_LAYOUT_WINDOW
