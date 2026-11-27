#pragma once

#include "crane_fn.h"
#include "crane_variant.h"
#include "shared_variant.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>

struct Nat {};

struct SharedVariantReuse {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::shared_box<tree> a0;
      uint64_t a1;
      uint64_t a2;
      crane::shared_box<tree> a3;
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

    static tree node(tree a0, uint64_t a1, uint64_t a2, tree a3) {
      return tree(Node{crane::shared_box<tree>::make(std::move(a0)), a1, a2,
                       crane::shared_box<tree>::make(std::move(a3))});
    }

    static tree node_crane_reuse(tree _tok, tree a0, uint64_t a1, uint64_t a2,
                                 tree a3) {
      auto _alt = Node{crane::shared_box<tree>::make(std::move(a0)), a1, a2,
                       crane::shared_box<tree>::make(std::move(a3))};
      if (_tok.v_.try_reuse(std::move(_alt))) {
        return _tok;
      }
      return tree(Node{std::move(_alt)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    std::optional<uint64_t> find(uint64_t k) const {
      // Loop replaces the tail recursion: each recursive call updates the loop
      // variables.
      const tree *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (crane::holds_alternative<typename tree::Leaf>(_sv.v())) {
          return std::optional<uint64_t>();
        } else {
          const auto &[a0, a1, a2, a3] =
              crane::get<typename tree::Node>(_sv.v());
          if (k < a1) {
            _loop_self = crane_raw(a0);
          } else if (a1 < k) {
            _loop_self = crane_raw(a3);
          } else {
            return std::make_optional<uint64_t>(a2);
          }
        }
      }
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
        uint64_t a2;
        const tree *a3;
      };

      struct _after_tree_rect_in_Node_2 {
        crane::shared_box<tree> a0;
        uint64_t a1;
        uint64_t a2;
        const tree *a3;
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
            const auto &[a0, a1, a2, a3] =
                crane::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(
                _after_tree_rect_in_Node{a0, a1, a2, crane_raw(a3)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (crane::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
          auto _f = std::move(crane::get<_after_tree_rect_in_Node>(_popped));
          _stack.pop_back();
          crane::shared_box<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          uint64_t a2 = _f.a2;
          const tree &a3 = *_f.a3;
          _stack.emplace_back(_after_tree_rect_in_Node_2{
              std::move(a0), a1, a2, &a3, std::move(_result)});
          _stack.emplace_back(_call{_f.a3});
        } else {
          auto _f = std::move(crane::get<_after_tree_rect_in_Node_2>(_popped));
          _stack.pop_back();
          crane::shared_box<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          uint64_t a2 = _f.a2;
          const tree &a3 = *_f.a3;
          _result =
              f0(*a0, std::move(_f._tmp2), a1, a2, a3, std::move(_result));
        }
      }
      return _result;
    }
  };

  static tree insert(uint64_t k, uint64_t v, tree t);

  struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      uint64_t a0;
      crane::shared_box<lst> a1;
    };

    using variant_t = crane::shared_variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Nil _v) : v_(_v) {}

    explicit lst(Cons _v) : v_(std::move(_v)) {}

    static lst nil() { return lst(Nil{}); }

    static lst cons(uint64_t a0, lst a1) {
      return lst(Cons{a0, crane::shared_box<lst>::make(std::move(a1))});
    }

    static lst cons_crane_reuse(lst _tok, uint64_t a0, lst a1) {
      auto _alt = Cons{a0, crane::shared_box<lst>::make(std::move(a1))};
      if (_tok.v_.try_reuse(std::move(_alt))) {
        return _tok;
      }
      return lst(Cons{std::move(_alt)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t total() const {
      const lst *_self = this;

      // Explicit stack replaces the non-tail recursion of total: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const lst *_self;
      };

      struct _after_total_in_Cons {
        uint64_t a0;
      };

      using _frame = std::variant<_call, _after_total_in_Cons>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (crane::holds_alternative<_call>(_popped)) {
          auto _f = std::move(crane::get<_call>(_popped));
          _stack.pop_back();
          const lst *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename lst::Nil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] = crane::get<typename lst::Cons>(_sv.v());
            _stack.emplace_back(_after_total_in_Cons{a0});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(crane::get<_after_total_in_Cons>(_popped));
          _stack.pop_back();
          uint64_t a0 = _f.a0;
          _result = a0 + _result;
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 lst_rec(T1 f, F1 &&f0) const {
      return this->template lst_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 lst_rect(T1 f, F1 &&f0) const {
      const lst *_self = this;

      // Explicit stack replaces the non-tail recursion of lst_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const lst *_self;
      };

      struct _after_lst_rect_in_Cons {
        uint64_t a0;
        crane::shared_box<lst> a1;
      };

      using _frame = std::variant<_call, _after_lst_rect_in_Cons>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (crane::holds_alternative<_call>(_popped)) {
          auto _f = std::move(crane::get<_call>(_popped));
          _stack.pop_back();
          const lst *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename lst::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = crane::get<typename lst::Cons>(_sv.v());
            _stack.emplace_back(_after_lst_rect_in_Cons{a0, a1});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(crane::get<_after_lst_rect_in_Cons>(_popped));
          _stack.pop_back();
          uint64_t a0 = _f.a0;
          crane::shared_box<lst> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static lst bump(lst l);
};
