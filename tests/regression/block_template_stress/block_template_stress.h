#ifndef INCLUDED_BLOCK_TEMPLATE_STRESS
#define INCLUDED_BLOCK_TEMPLATE_STRESS

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <system_error>
#include <utility>
#include <variant>

using namespace std::string_literals;

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>)
                          return crane_any_cast<A>(a);
                        else
                          return A(a);
                      }(),
                      l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct BlockTemplateStress {
  /// 1. Block template in a fixpoint body
  static List<std::string> read_n_lines(uint64_t n);
  /// 2. Block template inside a monadic if-then-else
  static std::string conditional_read(bool do_read);
  /// 3. Block template of non-string type (nat) in bind
  static uint64_t read_and_add();
  /// 4. Block template used in multiple match arms
  static std::string branch_read(uint64_t choice);
  /// 5. Block template in nested bind chain with arithmetic
  static uint64_t read_two_nats();
  /// 6. Block template result fed to another function
  static void block_result_as_arg();
  /// 9. Block template with %a0 inside a fixpoint
  static List<std::string> read_files(const List<std::string> &paths);
  /// 10. Block template interleaved with void calls
  static std::string interleaved_void();
};

#endif // INCLUDED_BLOCK_TEMPLATE_STRESS
