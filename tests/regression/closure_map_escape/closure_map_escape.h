#ifndef INCLUDED_CLOSURE_MAP_ESCAPE
#define INCLUDED_CLOSURE_MAP_ESCAPE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct ClosureMapEscape {
  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    mylist(const mylist<CraneU> &_other)
        : v_(crane_convert_spine(
              _other, std::shared_ptr<mylist<A>>(nullptr),
              [](const mylist<CraneU> &_cell) -> const mylist<CraneU> * {
                if (std::holds_alternative<typename mylist<CraneU>::Mycons>(
                        _cell.v())) {
                  return std::get<typename mylist<CraneU>::Mycons>(_cell.v())
                      .a1.get();
                } else {
                  return nullptr;
                }
              },
              [&](const mylist<CraneU> &_other,
                  std::shared_ptr<mylist<A>> _below) -> variant_t {
                if (std::holds_alternative<typename mylist<CraneU>::Mynil>(
                        _other.v())) {
                  return Mynil{};
                } else {
                  const auto &[a0, a1] =
                      std::get<typename mylist<CraneU>::Mycons>(_other.v());
                  return Mycons{
                      [&]() -> A {
                        if constexpr (crane_convertible<A, const CraneU &>) {
                          return crane_convert<A>(a0);
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
                return std::make_shared<mylist<A>>(std::move(_alt));
              })) {}

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist<A>(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist<A>> {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<mylist<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) = default;
    mylist &operator=(mylist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 mylist_rect(T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(a0, *a1, mylist_rect<T1, T2>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 mylist_rec(T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(a0, *a1, mylist_rec<T1, T2>(std::move(f), f0, *a1));
    }
  }

  /// Build a list of closures from a list of nats using LOCAL FIXPOINTS.
  /// Each recursive call creates a fixpoint add that captures the
  /// pattern variable h from the match.
  ///
  /// BUG: Each local fixpoint uses & capture. The pattern variable h
  /// is a local binding within the match IIFE. The fixpoint is stored in
  /// mycons (a constructor), so return_captures_by_value does NOT
  /// apply. After the match, h goes out of scope, and the closure
  /// references dangling memory.
  ///
  /// Difference from fix_escape_match: uses a USER-DEFINED list type
  /// (not stdlib option), and the fixpoints are built RECURSIVELY
  /// from list elements (not a single fixpoint).
  static mylist<crane::fn<uint64_t(uint64_t)>>
  map_to_adders(const mylist<uint64_t> &l);
  static uint64_t apply_first(const mylist<crane::fn<uint64_t(uint64_t)>> &fns,
                              uint64_t arg);
  static uint64_t sum_apply(const mylist<crane::fn<uint64_t(uint64_t)>> &fns,
                            uint64_t arg);
  /// test1: map_to_adders 10, 20, 30, apply first to 5.
  /// add(5) where add(x) = x + 10. So 10 + 5 = 15.
  /// Bug: h=10 captured by &, dangling after match.
  static constexpr uint64_t test1 = UINT64_C(15);
  /// test2: Sum of applying all adders to 0.
  /// (0+10) + (0+20) + (0+30) = 60.
  static constexpr uint64_t test2 = UINT64_C(60);
  /// test3: Build adders, noise, then apply.
  /// (1+100) + (1+200) = 302.
  static constexpr uint64_t test3 = UINT64_C(302);
};

#endif // INCLUDED_CLOSURE_MAP_ESCAPE
