#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <shared_array.h>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

#include "crane_bake.h"
extern const crane::bake::image crane_baked_table_6bda686fed62;
extern const crane::bake::image crane_baked_big_6a150784210f;
extern const crane::bake::image crane_baked_entries_9913efaaf321;

template <typename A> struct List;

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
};

struct String0 {
  static std::string append(const std::string &s1, std::string s2);
};

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &&>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of fold_right: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_fold_right_in_Cons {
      A a1;
    };

    using _frame = std::variant<_call, _after_fold_right_in_Cons>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = a0;
        } else {
          const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_fold_right_in_Cons{a1});
          _stack.emplace_back(_call{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<_after_fold_right_in_Cons>(_popped));
        _stack.pop_back();
        auto a1 = std::move(_f.a1);
        _result = f(a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct BakedConstantsDefault {
  template <typename T1, typename T2, typename F1>
  static T2 vec_rect(T2 f, F1 &&f0, const crane::shared_array<T1> &v) {
    if (v.empty()) {
      return f;
    } else {
      const T1 &a = v.front();
      crane::shared_array<T1> v0 = v.drop(1);
      return f0(a, v0, vec_rect<T1, T2>(std::move(f), f0, v0));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 vec_rec(T2 f, F1 &&f0, const crane::shared_array<T1> &v) {
    return vec_rect<T1, T2>(std::move(f), f0, v);
  }

  template <typename T1>
  static crane::shared_array<T1> vec_of_list(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return crane::shared_array<T1>{};
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return vec_of_list<T1>(*a1).push_front(a0);
    }
  }

  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> l;
      uint64_t x;
      std::shared_ptr<tree> r;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf() { return tree(Leaf{}); }

    static tree node(crane::shared_child_slot<tree> l, uint64_t x,
                     crane::shared_child_slot<tree> r) {
      return tree(Node{l.take(), x, r.take()});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->l && _alt->l.use_count() == 1) ||
              (_alt->r && _alt->r.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            _stack.push_back(std::move(_alt->l));
          }
          if (_alt->r && _alt->r.use_count() == 1) {
            _stack.push_back(std::move(_alt->r));
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

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[l0, x0, r0] = std::get<typename tree::Node>(t.v());
      return f0(*l0, tree_rect<T1>(f, f0, *l0), x0, *r0,
                tree_rect<T1>(f, f0, *r0));
    }
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(std::move(f), f0, t);
  }

  /// build n has 2^n - 1 nodes, but only n distinct ones: each node's
  /// two children are one value.
  static tree build(uint64_t n);
  static uint64_t size(const tree &t);
  static uint64_t sum_tree(const tree &t);
  /// Baked: a tree of 65535 nodes.
  [[gnu::used]] static inline const tree big =
      crane::bake::read<tree>(crane_baked_big_6a150784210f);
  /// Baked: a table of rows, two of them the same row.
  static crane::shared_array<uint64_t> row(uint64_t k);
  [[gnu::used]] static inline const std::pair<
      crane::shared_array<crane::shared_array<uint64_t>>,
      crane::shared_array<bool>> table = crane::bake::read<
      std::pair<crane::shared_array<crane::shared_array<uint64_t>>,
                crane::shared_array<bool>>>(crane_baked_table_6bda686fed62);

  /// Baked: a list of labelled records holding strings and options.
  struct entry {
    std::string name;
    std::optional<uint64_t> weight;
    tree label;
  };

  [[gnu::used]] static inline const List<entry> entries =
      crane::bake::read<List<entry>>(crane_baked_entries_9913efaaf321);
  static uint64_t big_size();
  static uint64_t big_sum();
  static uint64_t cell(uint64_t i, uint64_t j);
  static bool accept(uint64_t i);
  static std::string names();
  static uint64_t weights();
};
