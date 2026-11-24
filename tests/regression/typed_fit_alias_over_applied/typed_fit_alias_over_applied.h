#pragma once

#include "fn.h"
#include "shared_block.h"
#include <cstdint>
#include <utility>

struct TypedFitAliasOverApplied {
  template <typename a> using st = crane::fn<std::pair<a, uint64_t>(uint64_t)>;

  template <typename T1> static st<T1> sret(T1 a) {
    return [=, a = std::move(a)](uint64_t s) { return std::make_pair(a, s); };
  }

  template <typename T1, typename T2>
  static st<T2> sbind(std::type_identity_t<st<T1>> m,
                      std::type_identity_t<crane::fn<st<T2>(T1)>> f) {
    return [=, f = std::move(f), m = std::move(m)](uint64_t s) {
      auto [a, s_] = m(s);
      return crane::apply2(f, std::move(a), s_);
    };
  }

  static inline const st<uint64_t> sget =
      [](uint64_t s) { return std::make_pair(s, s); };
  static inline const st<bool> f2 = [](uint64_t eta0_) {
    // Built on the first call and immortal: every thread reads it without
    // touching its counts.
    static const auto sret_1 = crane::immortal(sret<bool>(true));
    return sret_1(eta0_);
  };
  static inline const st<uint64_t> f3 = [](uint64_t eta0_) {
    // Built on the first call and immortal: every thread reads it without
    // touching its counts.
    static const auto sbind_1 = crane::immortal(sbind<uint64_t, uint64_t>(
        sget, [](uint64_t n) { return sret<uint64_t>((n + UINT64_C(2))); }));
    return sbind_1(eta0_);
  };
  static inline const bool run = f2(UINT64_C(5)).first;
  static inline const uint64_t counter = f3(UINT64_C(5)).first;
};
