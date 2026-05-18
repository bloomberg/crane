#ifndef INCLUDED_MONADIC_CLOSURE
#define INCLUDED_MONADIC_CLOSURE

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::unique_ptr<List<A>> l;
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

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
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
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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
};

struct MonadicClosure {
  /// 1. Lambda capturing a bind result
  template <typename T1>
  static int64_t _capture_bind_f(const T1, const std::string line) {
    return static_cast<int64_t>(line.length());
  }

  static int64_t capture_bind();

  /// 2. Higher-order function taking a pure callback
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static T2 apply_after_effect(F0 &&f, const T1 &m) {
    T1 x = m;
    return f(x);
  }

  static int64_t test_apply_after();
  /// 3. Function returning a closure from monadic context
  static std::function<std::string(std::string)> make_greeter();

  /// 4. Passing effectful result to a HOF
  template <typename F0>
    requires std::is_invocable_r_v<int64_t, F0 &, int64_t &>
  static int64_t with_length(F0 &&f) {
    std::string line;
    std::getline(std::cin, line);
    return f(static_cast<int64_t>(line.length()));
  }

  static int64_t test_with_length();
  /// 5. Nested closures over bindings
  static int64_t nested_capture();

  /// 6. Closure used in a fold-like pattern
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, std::string &>
  static uint64_t count_matching(F0 &&pred, const List<std::string> &xs) {
    if (std::holds_alternative<typename List<std::string>::Nil>(xs.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<std::string>::Cons>(xs.v());
      uint64_t n = count_matching(pred, *a1);
      if (pred(a0)) {
        return (n + 1);
      } else {
        return n;
      }
    }
  }

  static uint64_t test_count();
  /// 7. Effect inside a let, result used later
  static int64_t let_effect_capture();
  /// 8. Two closures with different captured variables
  static std::pair<int64_t, int64_t> two_closures();
};

#endif // INCLUDED_MONADIC_CLOSURE
