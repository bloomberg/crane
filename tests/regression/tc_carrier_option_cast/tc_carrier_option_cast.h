#ifndef INCLUDED_TC_CARRIER_OPTION_CAST
#define INCLUDED_TC_CARRIER_OPTION_CAST

#include "crane_fn.h"
#include <any>
#include <concepts>
#include <memory>
#include <optional>
#include <utility>

template <typename I>
concept Box = requires {
  typename I::carrier;
  {
    I::wrap(std::declval<uint64_t>())
  } -> std::convertible_to<typename I::carrier>;
  {
    I::peek(std::declval<typename I::carrier>())
  } -> std::convertible_to<uint64_t>;
};

struct TcCarrierOptionCast {
  using carrier = std::any;

  struct OptBox {
    using carrier = std::optional<uint64_t>;

    static std::optional<uint64_t> wrap(uint64_t n) {
      return std::make_optional<uint64_t>(n);
    }

    static uint64_t peek(std::optional<uint64_t> o) {
      if (o.has_value()) {
        const uint64_t &n = *o;
        return n;
      } else {
        return UINT64_C(0);
      }
    }
  };

  static_assert(Box<OptBox>);
  static uint64_t test(uint64_t n);
};

#endif // INCLUDED_TC_CARRIER_OPTION_CAST
