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

struct RamAccessorNamespaceSafe {
  enum class port { ReadPort, WritePort };

  template <typename T1>
  static T1 port_rect(const T1 f, const T1 f0, const port p) {
    return [&](void) {
      switch (p) {
      case port::ReadPort: {
        return f;
      }
      case port::WritePort: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 port_rec(const T1 f, const T1 f0, const port p) {
    return [&](void) {
      switch (p) {
      case port::ReadPort: {
        return f;
      }
      case port::WritePort: {
        return f0;
      }
      }
    }();
  }

  static unsigned int read(const port x);

  static inline const unsigned int t =
      (read(port::ReadPort) + read(port::WritePort));
};
