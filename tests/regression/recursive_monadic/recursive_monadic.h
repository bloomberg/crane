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

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct RecursiveMonadic {
  /// 1. Simple recursive countdown with effect
  static unsigned int countdown(const unsigned int &n);
  /// 2. Recursive sum over list with logging
  static unsigned int sum_list(const List<unsigned int> &xs);
  /// 3. Recursive collect: transforms each element with effect
  static List<int64_t> collect_lengths(const List<std::string> &xs);
  /// 4. Recursive with two recursive calls (tree-like)
  static unsigned int repeat_action(const unsigned int &n,
                                    const std::string msg);

  /// 5. Recursive with match in the middle
  template <MapsTo<bool, unsigned int> F0>
  static List<unsigned int> filter_print(F0 &&pred,
                                         const List<unsigned int> &xs) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(xs.v());
      List<unsigned int> rest_ = filter_print(pred, *(d_a1));
      if (pred(d_a0)) {
        std::cout << "keep"s << '\n';
        return List<unsigned int>::cons(d_a0, rest_);
      } else {
        return rest_;
      }
    }
  }

  /// 6. Recursive with block template in each step
  static List<std::string> read_n_lines(const unsigned int &n);
  /// 7. Mutual-like: two functions calling each other via wrapper
  static std::string even_action(const unsigned int &n);
  static std::string odd_action(const unsigned int &n);

  /// 8. Recursive option-returning function
  template <MapsTo<bool, unsigned int> F0>
  static std::optional<unsigned int> find_first(F0 &&pred,
                                                const List<unsigned int> &xs) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
      return std::optional<unsigned int>();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(xs.v());
      std::cout << "checking"s << '\n';
      if (pred(d_a0)) {
        return std::make_optional<unsigned int>(d_a0);
      } else {
        return find_first(pred, *(d_a1));
      }
    }
  }
};

#endif // INCLUDED_RECURSIVE_MONADIC
