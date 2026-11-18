#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum;

struct Nat {};

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

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: generated program, shrunk by ephyra and delta-reduced
/// (unrelated-looking declarations kept are needed for the trigger).
///
/// Matching a sum value taken out of a pair literal (match fst (inl true, 0)
/// with inl u => .. | inr v => .. end, inside an applied observer) calls
/// v_mut() on a const Sum<bool, bool>: "function is not marked const". t_2 and
/// t_3 are the same shape at Sum<bool, uint64_t> and Sum<uint64_t, uint64_t>.
struct SumMatchConstVMut {
  struct stream {
    // TYPES
    template <typename CraneS0 = stream> struct SCons_ {
      uint64_t a0;
      CraneS0 a1;
    };

    using SCons = SCons_<>;
    using variant_t = std::variant<SCons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    stream() {}

    explicit stream(SCons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream scons(uint64_t a0, stream a1) {
      return stream(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, a0, std::move(a1)));
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream lazy_(F &&thunk) {
      return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static inline const uint64_t t_1 = []() {
    return []() {
      std::pair<Sum<bool, bool>, uint64_t> w7 =
          std::make_pair(Sum<bool, bool>::inl(true), UINT64_C(0));
      auto _once3 = (([&]() {
        const Sum<bool, bool> &w8 = w7.first;
        if (std::holds_alternative<typename Sum<bool, bool>::Inl>(w8.v())) {
          const auto &[a0] = std::get<typename Sum<bool, bool>::Inl>(w8.v());
          auto _once1 = ((a0 ? UINT64_C(1) : UINT64_C(2)) * UINT64_C(2));
          return (UINT64_C(10007) ? _once1 % UINT64_C(10007) : _once1);
        } else {
          const auto &[a0] = std::get<typename Sum<bool, bool>::Inr>(w8.v());
          auto _once2 =
              (((a0 ? UINT64_C(1) : UINT64_C(2)) * UINT64_C(2)) + UINT64_C(1));
          return (UINT64_C(10007) ? _once2 % UINT64_C(10007) : _once2);
        }
      }() * UINT64_C(5)) + w7.second);
      return (UINT64_C(10007) ? _once3 % UINT64_C(10007) : _once3);
    }();
  }();
  static inline const uint64_t t_2 = []() {
    return []() {
      std::pair<Sum<bool, uint64_t>, uint64_t> w7 =
          std::make_pair(Sum<bool, uint64_t>::inr(UINT64_C(6)), UINT64_C(3));
      auto _once3 = (([&]() {
        const Sum<bool, uint64_t> &w8 = w7.first;
        if (std::holds_alternative<typename Sum<bool, uint64_t>::Inl>(w8.v())) {
          const auto &[a0] =
              std::get<typename Sum<bool, uint64_t>::Inl>(w8.v());
          auto _once1 = ((a0 ? UINT64_C(1) : UINT64_C(2)) * UINT64_C(2));
          return (UINT64_C(10007) ? _once1 % UINT64_C(10007) : _once1);
        } else {
          const auto &[a0] =
              std::get<typename Sum<bool, uint64_t>::Inr>(w8.v());
          auto _once2 = ((a0 * UINT64_C(2)) + UINT64_C(1));
          return (UINT64_C(10007) ? _once2 % UINT64_C(10007) : _once2);
        }
      }() * UINT64_C(5)) + w7.second);
      return (UINT64_C(10007) ? _once3 % UINT64_C(10007) : _once3);
    }();
  }();
  static inline const uint64_t t_3 = []() {
    return []() {
      std::pair<Sum<uint64_t, uint64_t>, uint64_t> w7 = std::make_pair(
          Sum<uint64_t, uint64_t>::inl(UINT64_C(4)), UINT64_C(1));
      auto _once3 = (([&]() {
        const Sum<uint64_t, uint64_t> &w8 = w7.first;
        if (std::holds_alternative<typename Sum<uint64_t, uint64_t>::Inl>(
                w8.v())) {
          const auto &[a0] =
              std::get<typename Sum<uint64_t, uint64_t>::Inl>(w8.v());
          auto _once1 = (a0 * UINT64_C(2));
          return (UINT64_C(10007) ? _once1 % UINT64_C(10007) : _once1);
        } else {
          const auto &[a0] =
              std::get<typename Sum<uint64_t, uint64_t>::Inr>(w8.v());
          auto _once2 = ((a0 * UINT64_C(2)) + UINT64_C(1));
          return (UINT64_C(10007) ? _once2 % UINT64_C(10007) : _once2);
        }
      }() * UINT64_C(5)) + w7.second);
      return (UINT64_C(10007) ? _once3 % UINT64_C(10007) : _once3);
    }();
  }();
};
