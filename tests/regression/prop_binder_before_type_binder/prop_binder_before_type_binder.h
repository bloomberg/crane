#ifndef INCLUDED_PROP_BINDER_BEFORE_TYPE_BINDER
#define INCLUDED_PROP_BINDER_BEFORE_TYPE_BINDER

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Nat {
  static bool eq_dec(uint64_t n, uint64_t m);
};

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
};

struct PropBinderBeforeTypeBinder {
  template <typename T1> static T1 pick(T1 d, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return d;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  }

  static inline const uint64_t picked = pick<uint64_t>(
      UINT64_C(0), List<uint64_t>::cons(UINT64_C(5), List<uint64_t>::nil()));

  template <typename T1> static T1 pick2(const T1 &, T1 e) { return e; }

  static inline const uint64_t second =
      pick2<uint64_t>(UINT64_C(4), UINT64_C(5));

  template <typename A> struct guarded {
    // TYPES
    struct G {
      A a0;
    };

    struct N {};

    using variant_t = std::variant<G, N>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    guarded() {}

    explicit guarded(G _v) : v_(std::move(_v)) {}

    explicit guarded(N _v) : v_(_v) {}

    template <typename CraneU>
    guarded(const guarded<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename guarded<CraneU>::G>(
                    _other.v())) {
              const auto &[a0] =
                  std::get<typename guarded<CraneU>::G>(_other.v());
              return G{[&]() -> A {
                if constexpr (crane_convertible<A, const CraneU &>) {
                  return crane_convert<A>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              return N{};
            }
          }()) {}

    static guarded<A> g(A a0) { return guarded<A>(G{std::move(a0)}); }

    static guarded<A> n() { return guarded<A>(N{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &>
  static T2 guarded_rect(F0 &&f, T2 f0, const guarded<T1> &g) {
    if (std::holds_alternative<typename guarded<T1>::G>(g.v())) {
      const auto &[a0] = std::get<typename guarded<T1>::G>(g.v());
      return f(a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename T2, typename F0>
  static T2 guarded_rec(F0 &&f, T2 f0, const guarded<T1> &g) {
    return guarded_rect<T1, T2>(f, std::move(f0), g);
  }

  template <typename T1> static T1 gget(T1 d, const guarded<T1> &g) {
    if (std::holds_alternative<typename guarded<T1>::G>(g.v())) {
      const auto &[a0] = std::get<typename guarded<T1>::G>(g.v());
      return a0;
    } else {
      return d;
    }
  }

  static inline const uint64_t guard_sum =
      (gget<uint64_t>(UINT64_C(0), guarded<uint64_t>::g(UINT64_C(5))) +
       gget<uint64_t>(UINT64_C(7), guarded<uint64_t>::n()));

  template <typename T1, typename F0>
  static T1 sel(F0 &&dec, T1 def, uint64_t n, T1 a) {
    if (dec(n)) {
      return a;
    } else {
      return def;
    }
  }

  static inline const uint64_t selected =
      sel<uint64_t>([](uint64_t n) { return Nat::eq_dec(n, UINT64_C(2)); },
                    UINT64_C(0), UINT64_C(2), UINT64_C(6));
};

#endif // INCLUDED_PROP_BINDER_BEFORE_TYPE_BINDER
