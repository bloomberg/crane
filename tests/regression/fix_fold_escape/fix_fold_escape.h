#ifndef INCLUDED_FIX_FOLD_ESCAPE
#define INCLUDED_FIX_FOLD_ESCAPE

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct FixFoldEscape {
  /// Manual fold_left to avoid stdlib extraction complications.
  template <typename F0>
    requires std::is_invocable_r_v<
        List<std::function<uint64_t(uint64_t)>>, F0 &,
        List<std::function<uint64_t(uint64_t)>> &, uint64_t &>
  static List<std::function<uint64_t(uint64_t)>>
  fold_left(F0 &&f, List<std::function<uint64_t(uint64_t)>> acc,
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
  static List<std::function<uint64_t(uint64_t)>>
  collect_adders(const List<uint64_t> &l);
  static uint64_t apply_head(const List<std::function<uint64_t(uint64_t)>> &l,
                             uint64_t x);
  static uint64_t sum_apply(const List<std::function<uint64_t(uint64_t)>> &l,
                            uint64_t x); /// test1: collect_adders 10; 20; 30 ->
                                         /// adder_30; adder_20; adder_10
  /// (reversed by fold_left). apply_head picks adder_30, apply to 5 -> 35.
  static inline const uint64_t test1 = apply_head(
      collect_adders(List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(20),
              List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil())))),
      UINT64_C(5));
  /// test2: Sum all adders applied to 0.
  /// adder_30(0) + adder_20(0) + adder_10(0) = 30 + 20 + 10 = 60.
  static inline const uint64_t test2 = sum_apply(
      collect_adders(List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(20),
              List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil())))),
      UINT64_C(0));
  /// test3: With noise between collection and use.
  static inline const uint64_t test3 = []() {
    List<std::function<uint64_t(uint64_t)>> fns =
        collect_adders(List<uint64_t>::cons(
            UINT64_C(100),
            List<uint64_t>::cons(UINT64_C(200), List<uint64_t>::nil())));
    uint64_t noise = ((UINT64_C(55) + UINT64_C(44)) + UINT64_C(33));
    return (apply_head(std::move(fns), UINT64_C(0)) + noise);
  }();
};

#endif // INCLUDED_FIX_FOLD_ESCAPE
