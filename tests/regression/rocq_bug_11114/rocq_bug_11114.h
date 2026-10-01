#ifndef INCLUDED_ROCQ_BUG_11114
#define INCLUDED_ROCQ_BUG_11114

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct RocqBug11114 {
  struct t {
    // DATA
    uint64_t k;

    // ACCESSORS
    t clone() const { return {k}; }

    // CREATORS
    static t t0(uint64_t k) { return {k}; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 t_rect(const List<uint64_t> &, F1 &&f, const t &t0) {
    const auto &[k0] = t0;
    return f(k0);
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 t_rec(const List<uint64_t> &, F1 &&f, const t &t0) {
    const auto &[k0] = t0;
    return f(k0);
  }

  struct pkg {
    List<uint64_t> sig_;
    t t_;
  };

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static pkg map(F0 &&f, const pkg &p) {
    return pkg{p.sig_, [&]() {
                 const auto &_sv = p.t_;
                 const auto &[k0] = _sv;
                 return t::t0(f(k0));
               }()};
  }

  static inline const pkg test_pkg =
      pkg{List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()),
          t::t0(UINT64_C(2))};
  static inline const pkg test_map =
      map([](uint64_t x) { return (x + UINT64_C(1)); }, test_pkg);
};

#endif // INCLUDED_ROCQ_BUG_11114
