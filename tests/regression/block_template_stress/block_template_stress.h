#ifndef INCLUDED_BLOCK_TEMPLATE_STRESS
#define INCLUDED_BLOCK_TEMPLATE_STRESS

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

struct BlockTemplateStress {
  /// 1. Block template in a fixpoint body
  static List<std::string> read_n_lines(const unsigned int &n);
  /// 2. Block template inside a monadic if-then-else
  static std::string conditional_read(const bool &do_read);
  /// 3. Block template of non-string type (nat) in bind
  static unsigned int read_and_add();
  /// 4. Block template used in multiple match arms
  static std::string branch_read(const unsigned int &choice);
  /// 5. Block template in nested bind chain with arithmetic
  static unsigned int read_two_nats();
  /// 6. Block template result fed to another function
  static void block_result_as_arg();
  /// 9. Block template with %a0 inside a fixpoint
  static List<std::string> read_files(const List<std::string> &paths);
  /// 10. Block template interleaved with void calls
  static std::string interleaved_void();
};

#endif // INCLUDED_BLOCK_TEMPLATE_STRESS
