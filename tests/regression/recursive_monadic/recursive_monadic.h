#ifndef INCLUDED_RECURSIVE_MONADIC
#define INCLUDED_RECURSIVE_MONADIC

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;

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
};

struct RecursiveMonadic {
  /// 1. Simple recursive countdown with effect
  static uint64_t countdown(uint64_t n);
  /// 2. Recursive sum over list with logging
  static uint64_t sum_list(const List<uint64_t> &xs);
  /// 3. Recursive collect: transforms each element with effect
  static List<int64_t> collect_lengths(const List<std::string> &xs);
  /// 4. Recursive with two recursive calls (tree-like)
  static uint64_t repeat_action(uint64_t n, std::string msg);

  /// 5. Recursive with match in the middle
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> filter_print(F0 &&pred, const List<uint64_t> &xs) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
      return List<uint64_t>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
      List<uint64_t> rest_ = filter_print(pred, *a1);
      if (pred(a0)) {
        std::cout << "keep"s << '\n';
        return List<uint64_t>::cons(a0, std::move(rest_));
      } else {
        return rest_;
      }
    }
  }

  /// 6. Recursive with block template in each step
  static List<std::string> read_n_lines(uint64_t n);
  /// 7. Mutual-like: two functions calling each other via wrapper
  static std::string even_action(uint64_t n);
  static std::string odd_action(uint64_t n);

  /// 8. Recursive option-returning function
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static std::optional<uint64_t> find_first(F0 &&pred,
                                            const List<uint64_t> &xs) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
      return std::optional<uint64_t>();
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
      std::cout << "checking"s << '\n';
      if (pred(a0)) {
        return std::make_optional<uint64_t>(a0);
      } else {
        return find_first(pred, *a1);
      }
    }
  }
};

#endif // INCLUDED_RECURSIVE_MONADIC
