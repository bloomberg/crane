#ifndef INCLUDED_TYARG_PARTIAL_TYPE_APPLICATION
#define INCLUDED_TYARG_PARTIAL_TYPE_APPLICATION

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

template <typename I>
concept Mon = requires {
  typename I::template M<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template M<crane::obj>>;
  {
    I::template bnd<crane::obj, crane::obj>(
        std::declval<typename I::template M<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template M<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template M<crane::obj>>;
};

struct TyargPartialTypeApplication {
  template <typename T1, typename T2, typename F1>
  static std::optional<T2> bindo(const std::optional<T1> &o, F1 &&k) {
    if (o.has_value()) {
      const T1 &a = *o;
      return k(a);
    } else {
      return std::optional<T2>();
    }
  }

  template <typename T1, typename F1>
  static std::optional<T1> bind_nat(const std::optional<uint64_t> &x0_,
                                    F1 &&x1_) {
    return bindo<uint64_t, T1>(x0_, x1_);
  }

  static inline const std::optional<bool> bound =
      bind_nat<bool>(std::make_optional<uint64_t>(UINT64_C(3)), [](uint64_t n) {
        return std::make_optional<bool>(n == UINT64_C(3));
      });

  template <Mon _tcI0, typename T2>
  static typename _tcI0::template M<T2> ret(const T2 &x) {
    return _tcI0::template ret<T2>(x);
  }

  template <Mon _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template M<T3> bnd(typename _tcI0::template M<T2> x,
                                            F1 &&x0) {
    return _tcI0::template bnd<T2, T3>(std::move(x), x0);
  }

  struct Mon_option {
    template <typename CraneA0> using M = std::optional<CraneA0>;

    template <typename CraneA0> static std::optional<CraneA0> ret(CraneA0 a) {
      return std::make_optional<CraneA0>(std::move(a));
    }

    template <typename CraneA0, typename CraneA1>
    static std::optional<CraneA1>
    bnd(std::optional<CraneA0> o,
        crane::fn<std::optional<CraneA1>(CraneA0)> k) {
      if (o.has_value()) {
        const CraneA0 &a = *o;
        return k(a);
      } else {
        return std::optional<CraneA1>();
      }
    }
  };

  static_assert(Mon<Mon_option>);

  template <Mon _tcI0, typename T2, typename T3>
  static typename _tcI0::template M<T3>
  liftO(const std::type_identity_t<crane::fn<T3(T2)>> &f,
        typename _tcI0::template M<T2> m) {
    return _tcI0::template bnd<T2, T3>(std::move(m), [=](const T2 &a) {
      return _tcI0::template ret<T3>(f(a));
    });
  }

  template <typename T1, typename T2, typename F0>
  static std::optional<T2> lift_opt(F0 &&f, const std::optional<T1> &m) {
    return liftO<Mon_option, T1, T2>(f, m);
  }

  static inline const std::optional<uint64_t> lifted =
      lift_opt<uint64_t, uint64_t>([](uint64_t x) { return (x + 1); },
                                   std::make_optional<uint64_t>(UINT64_C(4)));

  template <typename T1> static std::pair<T1, T1> twice(const T1 &x) {
    return std::make_pair(x, x);
  }

  static inline const List<std::pair<uint64_t, uint64_t>> doubled =
      List<uint64_t>::cons(
          UINT64_C(1), List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil()))
          .template map<std::pair<uint64_t, uint64_t>>(twice<uint64_t>);

  static inline const uint64_t first_of_doubled = []() {
    auto &&_sv = doubled;
    if (std::holds_alternative<
            typename List<std::pair<uint64_t, uint64_t>>::Nil>(_sv.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(_sv.v());
      const auto &[a, _x0] = a0;
      return a;
    }
  }();
};

#endif // INCLUDED_TYARG_PARTIAL_TYPE_APPLICATION
