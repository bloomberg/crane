#ifndef INCLUDED_NON_UNIFORM_LIST_NEST
#define INCLUDED_NON_UNIFORM_LIST_NEST

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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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

struct NonUniformListNest {
  struct n2 {
    // TYPES
    struct Z2 {
      crane::obj a0;
    };

    struct S2 {
      std::shared_ptr<n2> a0;
    };

    using variant_t = std::variant<Z2, S2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    n2() {}

    explicit n2(Z2 _v) : v_(std::move(_v)) {}

    explicit n2(S2 _v) : v_(std::move(_v)) {}

    static n2 z2(crane::obj a0) { return n2(Z2{std::move(a0)}); }

    static n2 s2(n2 a0) { return n2(S2{std::make_shared<n2>(std::move(a0))}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2 = void, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const crane::obj &>
  static T1 n2_rect(F0 &&f, F1 &&f0, const n2 &n) {
    if (std::holds_alternative<typename n2::Z2>(n.v())) {
      const auto &[a0] = std::get<typename n2::Z2>(n.v());
      return crane_any_cast<T1>(f(a0));
    } else {
      const auto &[a0] = std::get<typename n2::S2>(n.v());
      return crane_any_cast<T1>(
          f0(*a0, n2_rect(crane_erase_fn<T1>(f), f0, *a0)));
    }
  }

  template <typename T1, typename T2 = void, typename F0, typename F1>
  static T1 n2_rec(F0 &&f, F1 &&f0, const n2 &n) {
    return n2_rect<T1, crane::obj>(crane_erase_fn<T1>(f), f0, n);
  }

  template <typename T1 = void> static uint64_t depth(const n2 &x) {
    if (std::holds_alternative<typename n2::Z2>(x.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0] = std::get<typename n2::S2>(x.v());
      return (depth<crane::obj>(*a0) + 1);
    }
  }

  static constexpr uint64_t go = UINT64_C(1);
};

#endif // INCLUDED_NON_UNIFORM_LIST_NEST
