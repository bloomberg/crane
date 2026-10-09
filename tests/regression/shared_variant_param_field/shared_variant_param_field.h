#ifndef INCLUDED_SHARED_VARIANT_PARAM_FIELD
#define INCLUDED_SHARED_VARIANT_PARAM_FIELD

#include "crane_fn.h"
#include "crane_variant.h"
#include "obj.h"
#include "shared_variant.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>

template <typename A> struct List;

struct Nat {};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    crane::shared_box<List<A>> l;
  };

  using variant_t = crane::shared_variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (crane::holds_alternative<typename List<CraneU>::Nil>(
                  _other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                crane::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{[&]() -> A {
                          if constexpr (crane_convertible<A, const CraneU &>) {
                            return crane_convert<A>(a);
                          } else {
                            throw std::logic_error(
                                "unreachable: inactive constructor field at "
                                "this instantiation");
                          }
                        }(),
                        (l ? crane::shared_box<List<A>>::make(
                                 crane_convert<List<A>>(*l))
                           : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(
        Cons{std::move(a), crane::shared_box<List<A>>::make(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = crane::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    crane::shared_box<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write
             ? *(*_write = crane::shared_box<List<T1>>::make(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = crane::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write =
                            crane::shared_box<List<T1>>::make(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &crane::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    crane::shared_box<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write
             ? *(*_write = crane::shared_box<List<A>>::make(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = crane::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node = (_write ? *(*_write = crane::shared_box<List<A>>::make(
                                         std::move(_cell)))
                                 : _root.emplace(std::move(_cell)));
        _write = &crane::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct SharedVariantParamField {
  template <typename A, typename B> struct step {
    // TYPES
    struct Done {
      A a0;
    };

    struct More {
      B a0;
    };

    struct Both {
      A a0;
      B a1;
    };

    using variant_t = crane::shared_variant<Done, More, Both>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    step() {}

    explicit step(Done _v) : v_(std::move(_v)) {}

    explicit step(More _v) : v_(std::move(_v)) {}

    explicit step(Both _v) : v_(std::move(_v)) {}

    template <typename CraneU0, typename CraneU1>
    step(const step<CraneU0, CraneU1> &_other)
        : v_([&]() -> variant_t {
            if (crane::holds_alternative<typename step<CraneU0, CraneU1>::Done>(
                    _other.v())) {
              const auto &[a0] =
                  crane::get<typename step<CraneU0, CraneU1>::Done>(_other.v());
              return Done{[&]() -> A {
                if constexpr (crane_convertible<A, const CraneU0 &>) {
                  return crane_convert<A>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              if (crane::holds_alternative<
                      typename step<CraneU0, CraneU1>::More>(_other.v())) {
                const auto &[a0] =
                    crane::get<typename step<CraneU0, CraneU1>::More>(
                        _other.v());
                return More{[&]() -> B {
                  if constexpr (crane_convertible<B, const CraneU1 &>) {
                    return crane_convert<B>(a0);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }()};
              } else {
                const auto &[a0, a1] =
                    crane::get<typename step<CraneU0, CraneU1>::Both>(
                        _other.v());
                return Both{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU0 &>) {
                        return crane_convert<A>(a0);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    [&]() -> B {
                      if constexpr (crane_convertible<B, const CraneU1 &>) {
                        return crane_convert<B>(a1);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }()};
              }
            }
          }()) {}

    static step<A, B> done(A a0) { return step<A, B>(Done{std::move(a0)}); }

    static step<A, B> more(B a0) { return step<A, B>(More{std::move(a0)}); }

    static step<A, B> both(A a0, B a1) {
      return step<A, B>(Both{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, typename F0, typename F1,
            typename F2>
    requires std::is_invocable_r_v<T3, F0 &, const T1 &> &&
             std::is_invocable_r_v<T3, F1 &, const T2 &> &&
             std::is_invocable_r_v<T3, F2 &, const T1 &, const T2 &>
  static T3 step_rect(F0 &&f, F1 &&f0, F2 &&f1, const step<T1, T2> &s) {
    if (crane::holds_alternative<typename step<T1, T2>::Done>(s.v())) {
      const auto &[a0] = crane::get<typename step<T1, T2>::Done>(s.v());
      return f(a0);
    } else if (crane::holds_alternative<typename step<T1, T2>::More>(s.v())) {
      const auto &[a0] = crane::get<typename step<T1, T2>::More>(s.v());
      return f0(a0);
    } else {
      const auto &[a0, a1] = crane::get<typename step<T1, T2>::Both>(s.v());
      return f1(a0, a1);
    }
  }

  template <typename T1, typename T2, typename T3, typename F0, typename F1,
            typename F2>
  static T3 step_rec(F0 &&f, F1 &&f0, F2 &&f1, const step<T1, T2> &s) {
    return step_rect<T1, T2, T3>(f, f0, f1, s);
  }

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<uint64_t, F0 &, const T1 &> &&
             std::is_invocable_r_v<uint64_t, F1 &, const T2 &>
  static uint64_t weight(F0 &&fa, F1 &&fb, const step<T1, T2> &s) {
    if (crane::holds_alternative<typename step<T1, T2>::Done>(s.v())) {
      const auto &[a0] = crane::get<typename step<T1, T2>::Done>(s.v());
      return fa(a0);
    } else if (crane::holds_alternative<typename step<T1, T2>::More>(s.v())) {
      const auto &[a0] = crane::get<typename step<T1, T2>::More>(s.v());
      return fb(a0);
    } else {
      const auto &[a0, a1] = crane::get<typename step<T1, T2>::Both>(s.v());
      return (fa(a0) + fb(a1));
    }
  }

  static uint64_t pair_sum(const std::pair<uint64_t, uint64_t> &p);
  static inline const List<step<std::pair<uint64_t, uint64_t>, List<uint64_t>>>
      steps = List<step<std::pair<uint64_t, uint64_t>, List<uint64_t>>>::cons(
          step<std::pair<uint64_t, uint64_t>, List<uint64_t>>::done(
              std::make_pair(UINT64_C(1), UINT64_C(2))),
          List<step<std::pair<uint64_t, uint64_t>, List<uint64_t>>>::cons(
              step<std::pair<uint64_t, uint64_t>, List<uint64_t>>::more(
                  List<uint64_t>::cons(
                      UINT64_C(3), List<uint64_t>::cons(
                                       UINT64_C(4), List<uint64_t>::nil()))),
              List<step<std::pair<uint64_t, uint64_t>, List<uint64_t>>>::cons(
                  step<std::pair<uint64_t, uint64_t>, List<uint64_t>>::both(
                      std::make_pair(UINT64_C(5), UINT64_C(6)),
                      List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil())),
                  List<step<std::pair<uint64_t, uint64_t>,
                            List<uint64_t>>>::nil())));

  static inline const uint64_t result =
      steps.app(steps)
          .template map<uint64_t>(
              [](step<std::pair<uint64_t, uint64_t>, List<uint64_t>> _x0)
                  -> uint64_t {
                return weight<std::pair<uint64_t, uint64_t>, List<uint64_t>>(
                    pair_sum,
                    [](const List<uint64_t> &l) {
                      return l.template fold_left<uint64_t>(
                          [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                            return (_x0 + _x1);
                          },
                          UINT64_C(0));
                    },
                    _x0);
              })
          .template fold_left<uint64_t>(
              [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                return (_x0 + _x1);
              },
              UINT64_C(0));
};

#endif // INCLUDED_SHARED_VARIANT_PARAM_FIELD
