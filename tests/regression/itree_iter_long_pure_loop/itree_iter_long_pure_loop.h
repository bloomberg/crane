#ifndef INCLUDED_ITREE_ITER_LONG_PURE_LOOP
#define INCLUDED_ITREE_ITER_LONG_PURE_LOOP

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <crane_itree.h>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum;

struct ItreeIterLongPureLoop {
  static std::shared_ptr<ITree<Sum<uint64_t, uint64_t>>> step(uint64_t n);
  static std::shared_ptr<ITree<uint64_t>> count_down(uint64_t n);
  static std::shared_ptr<ITree<uint64_t>> after_taus(uint64_t n);
};

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

  template <typename _U0, typename _U1>
  Sum(const Sum<_U0, _U1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<_U0, _U1>::Inl>(_other.v())) {
            const auto &[a0] =
                std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const _U0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const _U1 &>) {
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

#endif // INCLUDED_ITREE_ITER_LONG_PURE_LOOP
