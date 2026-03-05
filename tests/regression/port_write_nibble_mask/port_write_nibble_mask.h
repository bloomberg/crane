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

struct PortWriteNibbleMask {
  struct ram_chip {
    unsigned int chip_port;
  };

  static unsigned int chip_port(const std::shared_ptr<ram_chip> &r);

  static unsigned int nibble_of_nat(const unsigned int n);

  static std::shared_ptr<ram_chip>
  upd_port_in_chip(const std::shared_ptr<ram_chip> &_x, const unsigned int v);

  static inline const unsigned int t =
      upd_port_in_chip(
          std::make_shared<ram_chip>(ram_chip{0}),
          (((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1))
          ->chip_port;
};
