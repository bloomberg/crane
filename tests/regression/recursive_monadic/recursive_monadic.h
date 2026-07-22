#ifndef INCLUDED_RECURSIVE_MONADIC
#define INCLUDED_RECURSIVE_MONADIC

#include <any>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <system_error>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;

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
