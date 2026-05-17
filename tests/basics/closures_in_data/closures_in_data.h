#ifndef INCLUDED_CLOSURES_IN_DATA
#define INCLUDED_CLOSURES_IN_DATA

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return (*a2).template fold_left<T1>(f, f(a0, a1));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<T1>::cons(f(a0), (*a1).template map<T1>(f));
    }
  }
};

struct ClosuresInData {
  /// A list of functions: successor, doubling, and squaring.
  static inline const List<std::function<unsigned int(unsigned int)>> fn_list =
      List<std::function<unsigned int(unsigned int)>>::cons(
          [](unsigned int x) { return (x + 1); },
          List<std::function<unsigned int(unsigned int)>>::cons(
              [](unsigned int x) { return (x + x); },
              List<std::function<unsigned int(unsigned int)>>::cons(
                  [](unsigned int x) { return (x * x); },
                  List<std::function<unsigned int(unsigned int)>>::nil())));
  /// apply_all fns x applies every function in fns to x,
  /// returning the list of results.
  static List<unsigned int>
  apply_all(const List<std::function<unsigned int(unsigned int)>> &fns,
            unsigned int x);

  /// A pair of invertible transformations: forward and backward.
  struct transform {
    std::function<unsigned int(unsigned int)> forward;
    std::function<unsigned int(unsigned int)> backward;

    // ACCESSORS
    transform clone() const {
      return transform{(*this).forward, (*this).backward};
    }
  };

  /// A transform that doubles via addition and halves via division.
  static inline const transform double_transform =
      transform{[](unsigned int x) { return (x + x); },
                [](unsigned int x) { return (2u ? x / 2u : 0); }};
  static unsigned int apply_forward(const transform &t, unsigned int x);
  static unsigned int apply_backward(const transform &t, unsigned int x);
  /// compose_all fns x folds fns left, threading x through each
  /// function in sequence.
  static unsigned int
  compose_all(const List<std::function<unsigned int(unsigned int)>> &fns,
              unsigned int x);
  /// A pipeline of transformations: increment, double, then add 10.
  static inline const List<std::function<unsigned int(unsigned int)>> pipeline =
      List<std::function<unsigned int(unsigned int)>>::cons(
          [](unsigned int x) { return (x + 1u); },
          List<std::function<unsigned int(unsigned int)>>::cons(
              [](unsigned int x) { return (x * 2u); },
              List<std::function<unsigned int(unsigned int)>>::cons(
                  [](unsigned int x) { return (x + 10u); },
                  List<std::function<unsigned int(unsigned int)>>::nil())));
  /// maybe_apply mf x applies function mf to x if present,
  /// otherwise returns x unchanged.
  static unsigned int maybe_apply(
      const std::optional<std::function<unsigned int(unsigned int)>> &mf,
      unsigned int x);
  static inline const List<unsigned int> test_apply_all =
      apply_all(fn_list, 5u);
  static inline const unsigned int test_forward =
      apply_forward(double_transform, 7u);
  static inline const unsigned int test_backward =
      apply_backward(double_transform, 14u);
  static inline const unsigned int test_compose = compose_all(pipeline, 3u);
  static inline const unsigned int test_maybe_some =
      maybe_apply(std::make_optional<std::function<unsigned int(unsigned int)>>(
                      [](unsigned int x) { return (x + 1); }),
                  41u);
  static inline const unsigned int test_maybe_none = maybe_apply(
      std::optional<std::function<unsigned int(unsigned int)>>(), 42u);
};

#endif // INCLUDED_CLOSURES_IN_DATA
