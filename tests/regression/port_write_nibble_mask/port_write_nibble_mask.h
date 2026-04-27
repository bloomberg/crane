#ifndef INCLUDED_PORT_WRITE_NIBBLE_MASK
#define INCLUDED_PORT_WRITE_NIBBLE_MASK

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct PortWriteNibbleMask {
  struct ram_chip {
    unsigned int chip_port;

    __attribute__((pure)) ram_chip *operator->() { return this; }

    __attribute__((pure)) const ram_chip *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) ram_chip clone() const {
      return ram_chip{[](auto &&__v) -> unsigned int {
        if constexpr (
            requires { __v ? 0 : 0; } && requires { *__v; } &&
            requires { __v->clone(); } && requires { __v.get(); }) {
          using _E = std::remove_cvref_t<decltype(*__v)>;
          return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
        } else if constexpr (requires { __v.clone(); }) {
          return __v.clone();
        } else {
          return __v;
        }
      }((*this).chip_port)};
    }
  };

  __attribute__((pure)) static unsigned int
  nibble_of_nat(const unsigned int &n);
  __attribute__((pure)) static ram_chip upd_port_in_chip(const ram_chip &_x,
                                                         const unsigned int &v);
  static inline const unsigned int t =
      upd_port_in_chip(ram_chip{0u}, 31u).chip_port;
};

#endif // INCLUDED_PORT_WRITE_NIBBLE_MASK
