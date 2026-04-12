#ifndef INCLUDED_BLOCK_TEMPLATE_STRESS
#define INCLUDED_BLOCK_TEMPLATE_STRESS

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
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
  explicit List(Nil _v) : d_v_(_v) {}

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

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct BlockTemplateStress {
  /// 1. Block template in a fixpoint body
  static std::shared_ptr<List<std::string>> read_n_lines(const unsigned int n);
  /// 2. Block template inside a monadic if-then-else
  static std::string conditional_read(const bool do_read);
  /// 3. Block template of non-string type (nat) in bind
  static unsigned int read_and_add();
  /// 4. Block template used in multiple match arms
  static std::string branch_read(const unsigned int choice);
  /// 5. Block template in nested bind chain with arithmetic
  static unsigned int read_two_nats();
  /// 6. Block template result fed to another function
  static void block_result_as_arg();
  /// 9. Block template with %a0 inside a fixpoint
  static std::shared_ptr<List<std::string>>
  read_files(const std::shared_ptr<List<std::string>> &paths);

  /// 10. Block template interleaved with void calls
  static std::string interleaved_void();
};

#endif // INCLUDED_BLOCK_TEMPLATE_STRESS
