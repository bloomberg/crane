#ifndef INCLUDED_EVENT_PARAM_DROPPED
#define INCLUDED_EVENT_PARAM_DROPPED

#include "crane_fn.h"
#include <any>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum;
enum class Provenance;

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

  template <typename _U0, typename _U1> Sum(const Sum<_U0, _U1> &_other) {
    if (std::holds_alternative<typename Sum<_U0, _U1>::Inl>(_other.v())) {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
      this->v_ = Inl{[&]() -> A {
        if constexpr (crane_convertible<A, const _U0 &>) {
          return crane_convert<A>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    } else {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
      this->v_ = Inr{[&]() -> B {
        if constexpr (crane_convertible<B, const _U1 &>) {
          return crane_convert<B>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }
  }

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};
enum class Provenance { BUILD_PROVENANCE };
using prov = std::any;
template <typename I>
concept Params = requires {
  { I::PROV() } -> std::convertible_to<Provenance>;
};

struct Denotation {
  using exc = prov;

  struct FailE {
    // DATA
    exc a0;

    // ACCESSORS
    FailE clone() const { return {a0}; }

    // CREATORS
    static FailE fail(exc a0) { return {std::move(a0)}; }
  };
  enum class TickE { TICK };
  template <typename x = void> using E = Sum1<TickE, FailE, x>;

  template <Params _tcI0, typename T1 = void>
  static std::optional<exc>
  exc_of_event(const Sum1<TickE, FailE, std::any> &e) {
    if (std::holds_alternative<typename Sum1<TickE, FailE, std::any>::Inl1>(
            e.v())) {
      return std::optional<exc>();
    } else {
      const auto &[a0] =
          std::get<typename Sum1<TickE, FailE, std::any>::Inr1>(e.v());
      const auto &[a00] = a0;
      return std::make_optional<exc>(a00);
    }
  }

  template <Params _tcI0, typename T1>
  static std::shared_ptr<ITree<Sum<exc, T1>>>
  run_exc(const std::shared_ptr<ITree<T1>> &t) {
    return itree_iter(
        [](const std::shared_ptr<ITree<T1>> &u) {
          auto _cs = u->observe();
          if (std::holds_alternative<typename ITree<T1>::Ret>(_cs)) {
            const auto &_itf = *std::get_if<typename ITree<T1>::Ret>(&_cs);
            auto a = _itf.value;
            return itree_ret(
                Sum<std::shared_ptr<ITree<T1>>, Sum<std::any, T1>>::inr(
                    Sum<std::any, T1>::inr(a)));
          } else if (std::holds_alternative<typename ITree<T1>::Tau>(_cs)) {
            const auto &_itf = *std::get_if<typename ITree<T1>::Tau>(&_cs);
            auto u_ = _itf.next;
            return itree_ret(
                Sum<std::shared_ptr<ITree<T1>>, Sum<std::any, T1>>::inl(u_));
          } else {
            const auto &_itf = *std::get_if<typename ITree<T1>::Vis>(&_cs);
            auto e = crane_event_as<Sum1<TickE, FailE, std::any>>(_itf.effect);
            auto k = _itf.cont;
            auto _cs1 = exc_of_event(e);
            if (_cs1.has_value()) {
              const auto &x = *_cs1;
              return itree_ret(
                  Sum<std::shared_ptr<ITree<T1>>, Sum<std::any, T1>>::inr(
                      Sum<std::any, T1>::inl(x)));
            } else {
              return itree_vis(e, [=](const auto &y) mutable {
                return itree_ret(
                    Sum<std::shared_ptr<ITree<T1>>, Sum<std::any, T1>>::inl(
                        k(y)));
              });
            }
          }
        },
        t);
  }
};

struct EventParamDropped {
  template <Params _tcI0>
  static std::shared_ptr<ITree<Sum<prov, prov>>>
  use(const std::shared_ptr<ITree<prov>> &x1_) {
    return Denotation::template run_exc<_tcI0, prov>(x1_);
  }
};

#endif // INCLUDED_EVENT_PARAM_DROPPED
