#ifndef INCLUDED_MONADIC_VOID_EDGE
#define INCLUDED_MONADIC_VOID_EDGE

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

struct MonadicVoidEdge {
  /// 1. Bind where LHS is void and RHS returns a value
  static uint64_t bind_void_then_value();
  /// 2. Bind where both sides are void
  static void bind_void_void();
  /// 3. Let-binding the result of a monadic void call
  static uint64_t let_bind_monadic_void();
  /// 4. Passing unit through a chain of binds
  static void unit_chain();
  /// 5. Match on a value obtained from a bind
  static uint64_t match_after_bind();
  /// 6. Void function called in a non-tail bind position
  static std::string void_nontail();
  /// 7. Nested binds returning unit at every level
  static void deeply_nested_void();

  /// 8. Higher-order: pass a monadic void function as callback
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static void apply_effect(F0 &&f, uint64_t _x0) {
    f(_x0);
    return;
  }

  static void test_apply_effect();
  /// 9. Monadic function returning option unit
  static std::optional<std::monostate> maybe_print(bool b);
  /// 10. Bind result used in a pair
  static std::pair<uint64_t, uint64_t> bind_into_pair();
  /// 11. Void function result stored in list (should stay Unit, not void)
  static List<std::monostate> unit_in_list();
  /// 12. Mixed: some binds void, some value, interleaved
  static uint64_t mixed_binds();
  /// 13. Function that takes itree as argument and sequences
  static void sequence_effects(const std::monostate &e1,
                               const std::monostate &e2);
  static void test_sequence();
};

#endif // INCLUDED_MONADIC_VOID_EDGE
