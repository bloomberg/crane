#ifndef INCLUDED_FIX_FOLD_ESCAPE
#define INCLUDED_FIX_FOLD_ESCAPE

#include "crane_fn.h"
#include "fn.h"
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

struct FixFoldEscape {
  /// Manual fold_left to avoid stdlib extraction complications.
  template <typename F0>
    requires std::is_invocable_r_v<List<crane::fn<uint64_t(uint64_t)>>, F0 &,
                                   List<crane::fn<uint64_t(uint64_t)>> &&,
                                   const uint64_t &>
  static List<crane::fn<uint64_t(uint64_t)>>
  fold_left(F0 &&f, List<crane::fn<uint64_t(uint64_t)>> acc,
            const List<uint64_t> &l) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return acc;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      return fold_left(f, f(std::move(acc), a0), *a1);
    }
  }

  /// Collect fixpoint closures by folding over a list of nats.
  /// Each iteration creates a new fixpoint adder that captures the
  /// current element n from the fold callback's parameter.
  ///
  /// BUG HYPOTHESIS: The callback lambda's parameter n lives on the
  /// callback's stack frame. The fixpoint adder captures n by &.
  /// The callback returns cons adder acc, storing the closure.
  /// After the callback returns, n is destroyed. Later iterations and
  /// the final result contain dangling closures.
  static List<crane::fn<uint64_t(uint64_t)>>
  collect_adders(const List<uint64_t> &l);
  static uint64_t apply_head(const List<crane::fn<uint64_t(uint64_t)>> &l,
                             uint64_t x);
  static uint64_t sum_apply(const List<crane::fn<uint64_t(uint64_t)>> &l,
                            uint64_t x);
  /// test1: collect_adders 10; 20; 30 -> adder_30; adder_20; adder_10
  /// (reversed by fold_left). apply_head picks adder_30, apply to 5 -> 35.
  static constexpr uint64_t test1 = UINT64_C(35);
  /// test2: Sum all adders applied to 0.
  /// adder_30(0) + adder_20(0) + adder_10(0) = 30 + 20 + 10 = 60.
  static constexpr uint64_t test2 = UINT64_C(60);
  /// test3: With noise between collection and use.
  static constexpr uint64_t test3 = UINT64_C(332);
};

#endif // INCLUDED_FIX_FOLD_ESCAPE
