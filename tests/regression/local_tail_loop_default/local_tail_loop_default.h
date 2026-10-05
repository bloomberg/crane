#ifndef INCLUDED_LOCAL_TAIL_LOOP_DEFAULT
#define INCLUDED_LOCAL_TAIL_LOOP_DEFAULT

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

struct LocalTailLoopDefault {
  /// A tail-recursive local fixpoint becomes a loop without Crane Loopify:
  /// its call depth is bounded however long the input, and it is an ordinary
  /// lambda rather than a self-applying one.
  static uint64_t sum_to(uint64_t n);

  /// The accumulator is an owned loop variable, rebuilt on every step.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &>
  static List<uint64_t> rev_map(F0 &&f, const List<uint64_t> &l) {
    {
      const List<uint64_t> &_lc1_l0 = l;
      List<uint64_t> _lc1_acc = List<uint64_t>::nil();
      List<uint64_t> _lc1_loop_acc = std::move(_lc1_acc);
      const List<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
      while (true) {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _lc1_loop_l0->v())) {
          return _lc1_loop_acc;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(_lc1_loop_l0->v());
          _lc1_loop_acc = List<uint64_t>::cons(f(a0), std::move(_lc1_loop_acc));
          _lc1_loop_l0 = crane_raw(a1);
        }
      }
    }
  }
};

#endif // INCLUDED_LOCAL_TAIL_LOOP_DEFAULT
