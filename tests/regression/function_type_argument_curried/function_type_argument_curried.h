#ifndef INCLUDED_FUNCTION_TYPE_ARGUMENT_CURRIED
#define INCLUDED_FUNCTION_TYPE_ARGUMENT_CURRIED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "shared_block.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Nat {};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

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
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

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
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct FunctionTypeArgumentCurried {
  template <typename T1> static T1 idp(T1 x) { return x; }

  static uint64_t f2(uint64_t x0_, uint64_t x1_);

  template <typename T1> static List<T1> wrap(const T1 &x) {
    return List<T1>::cons(x, List<T1>::nil());
  }

  static inline const List<crane::fn<uint64_t(uint64_t, uint64_t)>> ws = []() {
    return crane_convert<List<crane::fn<uint64_t(uint64_t, uint64_t)>>>(
        wrap<crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>>(
            [](uint64_t _x0) {
              return [=](uint64_t _x1) -> uint64_t { return (_x0 + _x1); };
            }));
  }();
  static inline const uint64_t from_wrap = []() {
    auto &&_sv = ws;
    if (std::holds_alternative<
            typename List<crane::fn<uint64_t(uint64_t, uint64_t)>>::Nil>(
            _sv.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<
          typename List<crane::fn<uint64_t(uint64_t, uint64_t)>>::Cons>(
          _sv.v());
      return a0(UINT64_C(3), UINT64_C(4));
    }
  }();

  struct t {
    // DATA
    uint64_t a0;
    uint64_t a1;
    uint64_t a2;

    // ACCESSORS
    t clone() const { return {a0, a1, a2}; }

    // CREATORS
    static t a(uint64_t a0, uint64_t a1, uint64_t a2) { return {a0, a1, a2}; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &, const uint64_t &,
                                   const uint64_t &>
  static T1 t_rect(F0 &&f, const t &t0) {
    const auto &[a0, a1, a2] = t0;
    return f(a0, a1, a2);
  }

  template <typename T1, typename F0> static T1 t_rec(F0 &&f, const t &t0) {
    return t_rect<T1>(f, t0);
  }

  static uint64_t ev(const t &x);
  static inline const List<crane::fn<t(uint64_t, uint64_t)>> fs = []() {
    return crane_convert<List<crane::fn<t(uint64_t, uint64_t)>>>(
        List<uint64_t>::cons(
            UINT64_C(1),
            List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil()))
            .template map<crane::fn<crane::fn<t(uint64_t)>(uint64_t)>>(
                [](uint64_t x) {
                  return [=](uint64_t x0) {
                    return [=](uint64_t x1) { return t::a(x, x0, x1); };
                  };
                }));
  }();
  static inline const uint64_t from_ctor = fs.template fold_left<uint64_t>(
      [](uint64_t acc, const crane::fn<t(uint64_t, uint64_t)> &f) {
        return (acc + ev(f(UINT64_C(0), UINT64_C(5))));
      },
      UINT64_C(0));

  template <typename T1, typename T2> static T1 myfst(std::pair<T1, T2> p) {
    auto [a, _x] = std::move(p);
    return a;
  }

  static inline const std::pair<crane::fn<uint64_t(uint64_t, uint64_t)>,
                                uint64_t>
      pf = std::make_pair(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          UINT64_C(1));
  static inline const uint64_t from_pair =
      myfst<crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>, uint64_t>(
          crane_convert<std::pair<
              crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>, uint64_t>>(
              pf))(UINT64_C(2))(UINT64_C(3));
  static inline const uint64_t result =
      (((f2(UINT64_C(1), UINT64_C(2)) + from_wrap) + from_ctor) + from_pair);
};

#endif // INCLUDED_FUNCTION_TYPE_ARGUMENT_CURRIED
