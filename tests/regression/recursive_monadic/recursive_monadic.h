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
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct RecursiveMonadic {
  /// 1. Simple recursive countdown with effect
  static unsigned int countdown(const unsigned int n);
  /// 2. Recursive sum over list with logging
  static unsigned int sum_list(const std::shared_ptr<List<unsigned int>> &xs);
  /// 3. Recursive collect: transforms each element with effect
  static std::shared_ptr<List<int64_t>>
  collect_lengths(const std::shared_ptr<List<std::string>> &xs);
  /// 4. Recursive with two recursive calls (tree-like)
  static unsigned int repeat_action(const unsigned int n,
                                    const std::string msg);

  /// 5. Recursive with match in the middle
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  filter_print(F0 &&pred, const std::shared_ptr<List<unsigned int>> &xs) {
    return std::visit(
        Overloaded{[](const typename List<unsigned int>::Nil _args)
                       -> std::shared_ptr<List<unsigned int>> {
                     return List<unsigned int>::nil();
                   },
                   [&](const typename List<unsigned int>::Cons _args)
                       -> std::shared_ptr<List<unsigned int>> {
                     std::shared_ptr<List<unsigned int>> rest_ =
                         filter_print(pred, _args.d_a1);
                     if (pred(_args.d_a0)) {
                       std::cout << "keep"s << '\n';
                       return List<unsigned int>::cons(_args.d_a0, rest_);
                     } else {
                       return rest_;
                     }
                   }},
        xs->v());
  }

  /// 6. Recursive with block template in each step
  static std::shared_ptr<List<std::string>> read_n_lines(const unsigned int n);
  /// 7. Mutual-like: two functions calling each other via wrapper
  static std::string even_action(const unsigned int n);
  static std::string odd_action(const unsigned int n);

  /// 8. Recursive option-returning function
  template <MapsTo<bool, unsigned int> F0>
  static std::optional<unsigned int>
  find_first(F0 &&pred, const std::shared_ptr<List<unsigned int>> &xs) {
    return std::visit(
        Overloaded{[](const typename List<unsigned int>::Nil _args)
                       -> std::optional<unsigned int> {
                     return std::optional<unsigned int>();
                   },
                   [&](const typename List<unsigned int>::Cons _args)
                       -> std::optional<unsigned int> {
                     std::cout << "checking"s << '\n';
                     if (pred(_args.d_a0)) {
                       return std::make_optional<unsigned int>(_args.d_a0);
                     } else {
                       return find_first(pred, _args.d_a1);
                     }
                   }},
        xs->v());
  }
};

#endif // INCLUDED_RECURSIVE_MONADIC
