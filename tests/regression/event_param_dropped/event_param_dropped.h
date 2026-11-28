#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum;
enum class Provenance;
using prov = crane::obj;
template <typename I>
concept Params = requires {
  { I::PROV() } -> std::convertible_to<Provenance>;
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

/// An event family defined under a class Context (FailE carries the
/// class's prov), observed by ITree.iter in run_exc.  The name
/// records the defect it was written for, an event parameter dropped.
/// Added without a dune stanza in 0fb638f2a; it extracts, compiles and
/// runs.
enum class Provenance { BUILD_PROVENANCE };

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
  template <typename x> using E = Sum1<TickE, FailE, x>;

  template <Params _tcI0, typename T1>
  static std::optional<exc> exc_of_event(const Sum1<TickE, FailE, T1> &e) {
    if (std::holds_alternative<typename std::decay_t<decltype(e)>::Inl1>(e.v())) {
      const auto &_x =
          std::get<typename std::decay_t<decltype(e)>::Inl1>(e.v()).a0;
      return std::optional<exc>();
    } else {
      const auto &f =
          std::get<typename std::decay_t<decltype(e)>::Inr1>(e.v()).a0;
      const auto &[a0] = f;
      return std::make_optional<exc>(a0);
    }
  }

  template <Params _tcI0, typename T1>
  static std::shared_ptr<ITree<Sum<exc, T1>>>
  run_exc(const std::shared_ptr<ITree<T1>> &t) {
    return itree_iter(
        [](const std::shared_ptr<ITree<T1>> &u) -> std::shared_ptr<
            ITree<Sum<std::shared_ptr<ITree<T1>>, Sum<exc, T1>>>> {
          auto _cs = u->observe();
          if (std::holds_alternative<typename ITree<T1>::Ret>(_cs)) {
            T1 a = std::get_if<typename ITree<T1>::Ret>(&_cs)->value;
            return itree_ret(
                Sum<std::shared_ptr<ITree<T1>>, Sum<crane::obj, T1>>::inr(
                    Sum<crane::obj, T1>::inr(std::move(a))));
          } else if (std::holds_alternative<typename ITree<T1>::Tau>(_cs)) {
            auto u_ = std::get_if<typename ITree<T1>::Tau>(&_cs)->next;
            return itree_ret(
                Sum<std::shared_ptr<ITree<T1>>, Sum<crane::obj, T1>>::inl(
                    std::move(u_)));
          } else {
            auto e = crane_event_as<Sum1<TickE, FailE, crane::obj>>(
                std::get_if<typename ITree<T1>::Vis>(&_cs)->effect);
            auto k = std::get_if<typename ITree<T1>::Vis>(&_cs)->cont;
            auto _cs1 = exc_of_event<_tcI0>(e);
            if (_cs1.has_value()) {
              const auto &x = *_cs1;
              return itree_ret(
                  Sum<std::shared_ptr<ITree<T1>>, Sum<crane::obj, T1>>::inr(
                      Sum<crane::obj, T1>::inl(x)));
            } else {
              return itree_vis(
                  std::move(e), [=, k = std::move(k)](const auto &y) {
                    return itree_ret(
                        Sum<std::shared_ptr<ITree<T1>>,
                            Sum<crane::obj, T1>>::inl(crane_call_erased(k, y)));
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
