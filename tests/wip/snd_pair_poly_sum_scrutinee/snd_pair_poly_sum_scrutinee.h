#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum;

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1>
  Sum(const Sum<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<CraneU0, CraneU1>::Inl>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const CraneU1 &>) {
                return crane_convert<B>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct SndPairPolySumScrutinee {
  struct pt {
    uint64_t px;
    bool py;
  };

  template <typename T1> static uint64_t f(const T1 &) {
    std::pair<uint64_t, Sum<T1, pt>> pp =
        std::make_pair(UINT64_C(0), Sum<T1, pt>::inr(pt{UINT64_C(0), true}));
    auto sb = std::move(pp).second;
    if (std::holds_alternative<typename Sum<crane::obj, pt>::Inl>(sb.v_mut())) {
      return UINT64_C(1);
    } else {
      return UINT64_C(2);
    }
  }

  static inline const uint64_t result = f<bool>(true);
};
