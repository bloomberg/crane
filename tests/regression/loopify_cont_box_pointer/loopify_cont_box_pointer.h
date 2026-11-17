#ifndef INCLUDED_LOOPIFY_CONT_BOX_POINTER
#define INCLUDED_LOOPIFY_CONT_BOX_POINTER

#include "crane_fn.h"
#include "crane_variant.h"
#include "fn.h"
#include "obj.h"
#include "shared_variant.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <stdexcept>
#include <type_traits>
#include <utility>

template <typename A> struct List;

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
};

struct Nat {};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    crane::shared_box<List<A>> l;
  };

  using variant_t = crane::shared_variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (crane::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                crane::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? crane::shared_box<List<A>>::make(
                         crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(
        Cons{std::move(a), crane::shared_box<List<A>>::make(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = crane::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }
};

struct LoopifyContBoxPointer {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::shared_box<tree> a0;
      uint64_t a1;
      crane::shared_box<tree> a2;
    };

    using variant_t = crane::shared_variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{crane::shared_box<tree>::make(std::move(a0)), a1,
                       crane::shared_box<tree>::make(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t sum() const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of sum: _call frames are
      // pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_sum_in_Node {
        uint64_t a1;
        const tree *a2;
      };

      struct _after_sum_in_Node_2 {
        uint64_t a1;
        uint64_t _tmp2;
      };

      using _frame =
          std::variant<_call, _after_sum_in_Node, _after_sum_in_Node_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (crane::holds_alternative<_call>(_popped)) {
          auto _f = std::move(crane::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = crane::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_sum_in_Node{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (crane::holds_alternative<_after_sum_in_Node>(_popped)) {
          auto _f = std::move(crane::get<_after_sum_in_Node>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_sum_in_Node_2{a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(crane::get<_after_sum_in_Node_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          _result = ((_f._tmp2 + a1) + std::move(_result));
        }
      }
      return _result;
    }

    tree insert(uint64_t k) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of insert: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_insert_in_true {
        uint64_t a1;
        crane::shared_box<tree> a2;
      };

      struct _after_insert_in_true_2 {
        crane::shared_box<tree> a0;
        uint64_t a1;
      };

      using _frame =
          std::variant<_call, _after_insert_in_true, _after_insert_in_true_2>;
      tree _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (crane::holds_alternative<_call>(_popped)) {
          auto _f = std::move(crane::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = tree::node(tree::leaf(), k, tree::leaf());
          } else {
            const auto &[a0, a1, a2] = crane::get<typename tree::Node>(_sv.v());
            if (k < a1) {
              _stack.emplace_back(_after_insert_in_true{a1, a2});
              _stack.emplace_back(_call{crane_raw(a0)});
            } else {
              if (a1 < k) {
                _stack.emplace_back(_after_insert_in_true_2{a0, a1});
                _stack.emplace_back(_call{crane_raw(a2)});
              } else {
                _result = *_self;
              }
            }
          }
        } else if (crane::holds_alternative<_after_insert_in_true>(_popped)) {
          auto _f = std::move(crane::get<_after_insert_in_true>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          crane::shared_box<tree> a2 = std::move(_f.a2);
          _result = tree::node(std::move(_result), a1, *a2);
        } else {
          auto _f = std::move(crane::get<_after_insert_in_true_2>(_popped));
          _stack.pop_back();
          crane::shared_box<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          _result = tree::node(*a0, a1, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 tree_rec(T1 f, F1 &&f0) const {
      return this->template tree_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tree_rect_in_Node {
        crane::shared_box<tree> a0;
        uint64_t a1;
        const tree *a2;
      };

      struct _after_tree_rect_in_Node_2 {
        crane::shared_box<tree> a0;
        uint64_t a1;
        const tree *a2;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_tree_rect_in_Node,
                                  _after_tree_rect_in_Node_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (crane::holds_alternative<_call>(_popped)) {
          auto _f = std::move(crane::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = crane::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_rect_in_Node{a0, a1,
                                                         crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (crane::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
          auto _f = std::move(crane::get<_after_tree_rect_in_Node>(_popped));
          _stack.pop_back();
          crane::shared_box<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_tree_rect_in_Node_2{std::move(a0), a1, &a2,
                                                         std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(crane::get<_after_tree_rect_in_Node_2>(_popped));
          _stack.pop_back();
          crane::shared_box<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  static tree build(uint64_t n);

  /// Read through a closure, which is what makes sum a method.
  struct reader {
    // DATA
    crane::fn<uint64_t(uint64_t)> a0;

    // ACCESSORS
    reader clone() const { return {a0}; }

    // CREATORS
    static reader reader0(crane::fn<uint64_t(uint64_t)> a0) {
      return {std::move(a0)};
    }

    uint64_t read(uint64_t x) const {
      const auto &[a0] = *this;
      return a0(x);
    }

    template <typename T1, typename F0> T1 reader_rec(F0 &&f) const {
      return this->template reader_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     const crane::fn<uint64_t(uint64_t)> &>
    T1 reader_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  static reader read_with(tree t);
  static inline const uint64_t total =
      read_with(build(UINT64_C(20))).read(UINT64_C(0));
};

#endif // INCLUDED_LOOPIFY_CONT_BOX_POINTER
