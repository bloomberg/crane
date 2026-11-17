#pragma once

#include <concepts>
#include <cstdint>

template <typename M>
concept S = requires {
  requires (requires {
    {
      M::n
    }
    -> std::convertible_to<uint64_t>;
  } || requires {
    {
      M::n()
    }
    -> std::convertible_to<uint64_t>;
  });
};

struct RocqBug20989 {
  struct A {
    static constexpr uint64_t n = UINT64_C(0);
  };

  template <S X> struct M {
    using In = X;

    static const uint64_t &n() {
      static const uint64_t v = In::n;
      return v;
    }
  };

  using N = M<A>;
};
