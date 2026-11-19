#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum;
template <typename A> struct List;
struct Ascii;
struct String;

struct Nat {};

struct N {};

struct Ascii0 {
  static unsigned int N_of_digits(const List<bool> &l);
  static unsigned int N_of_ascii(const Ascii &a);
  static uint64_t nat_of_ascii(const Ascii &a);
};

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1>
  Sum(const Sum<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<CraneU0, CraneU1>::Inl>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const CraneU1 &>) {
                return crane_convert<B>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
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
};

struct Ascii {
  // DATA
  bool a0;
  bool a1;
  bool a2;
  bool a3;
  bool a4;
  bool a5;
  bool a6;
  bool a7;

  // ACCESSORS
  Ascii clone() const { return {a0, a1, a2, a3, a4, a5, a6, a7}; }

  // CREATORS
  static Ascii ascii0(bool a0, bool a1, bool a2, bool a3, bool a4, bool a5,
                      bool a6, bool a7) {
    return {a0, a1, a2, a3, a4, a5, a6, a7};
  }
};

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii a0;
    std::shared_ptr<String> a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : v_(_v) {}

  explicit String(String0 _v) : v_(std::move(_v)) {}

  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii a0, crane::shared_child_slot<String> a1) {
    return String(String0{std::move(a0), a1.take()});
  }

  // MANIPULATORS
  ~String() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<String> {
      if (auto *_alt = std::get_if<String0>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a1);
        }
      }
      return nullptr;
    };
    std::shared_ptr<String> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  String(const String &) = default;
  String &operator=(const String &) = default;
  String(String &&) = default;
  String &operator=(String &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const String *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const String *_self;
    };

    struct _after_length_in_String0 {};

    using _frame = std::variant<_call, _after_length_in_String0>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const String *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename String::String0>(_sv.v());
          _stack.emplace_back(_after_length_in_String0{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_String0>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  std::optional<Ascii> get(uint64_t n) const;
  String substring(uint64_t n, uint64_t m) const;
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: generated program, shrunk by ephyra and delta-reduced
/// (unrelated-looking declarations kept are needed for the trigger).
///
/// In a constrained polymorphic definition, pmap over a ptree (sum tree A)
/// literal holding inr a20 builds Sum<crane::obj, ...> where a uint64_t is
/// expected ("no viable conversion from 'Sum<crane::obj, unsigned long
/// long>'").

template <typename I, typename A>
concept Sz = requires {
  { I::sz(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct PolySumPayloadObj {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
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

    static tree node(crane::shared_child_slot<tree> a0, uint64_t a1,
                     crane::shared_child_slot<tree> a2) {
      return tree(Node{a0.take(), a1, a2.take()});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
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
        std::shared_ptr<tree> a0;
        uint64_t a1;
        const tree *a2;
      };

      struct _after_tree_rect_in_Node_2 {
        std::shared_ptr<tree> a0;
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
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_rect_in_Node{a0, a1,
                                                         crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_tree_rect_in_Node>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_tree_rect_in_Node_2{std::move(a0), a1, &a2,
                                                         std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_tree_rect_in_Node_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct pt {
    uint64_t px;
    bool py;
  };

  struct sz_nat {
    constexpr static uint64_t sz(uint64_t n) { return n; }
  };

  static_assert(Sz<sz_nat, uint64_t>);

  template <typename A> struct ptree {
    // TYPES
    struct PLeaf {};

    struct PNode {
      std::shared_ptr<ptree<A>> a0;
      A a1;
      std::shared_ptr<ptree<A>> a2;
    };

    using variant_t = std::variant<PLeaf, PNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ptree() {}

    explicit ptree(PLeaf _v) : v_(_v) {}

    explicit ptree(PNode _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    ptree(const ptree<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename ptree<CraneU>::PLeaf>(
                    _other.v())) {
              return PLeaf{};
            } else {
              const auto &[a0, a1, a2] =
                  std::get<typename ptree<CraneU>::PNode>(_other.v());
              return PNode{
                  (a0 ? std::make_shared<ptree<A>>(crane_convert<ptree<A>>(*a0))
                      : nullptr),
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a1);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (a2 ? std::make_shared<ptree<A>>(crane_convert<ptree<A>>(*a2))
                      : nullptr)};
            }
          }()) {}

    static ptree<A> pleaf() { return ptree<A>(PLeaf{}); }

    static ptree<A> pnode(crane::shared_child_slot<ptree<A>> a0, A a1,
                          crane::shared_child_slot<ptree<A>> a2) {
      return ptree<A>(PNode{a0.take(), std::move(a1), a2.take()});
    }

    // MANIPULATORS
    ~ptree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<PLeaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<PNode>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<ptree<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<PNode>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
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

    ptree(const ptree &) = default;
    ptree &operator=(const ptree &) = default;
    ptree(ptree &&) = default;
    ptree &operator=(ptree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, T1 &&, A &>
    T1 pfold(F0 &&f, T1 acc) const {
      const ptree<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of pfold: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const ptree<A> *_self;
        T1 acc;
      };

      struct _after_pfold_in_PNode {
        A a1;
        const ptree<A> *a2;
      };

      using _frame = std::variant<_call, _after_pfold_in_PNode>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self, std::move(acc)});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const ptree<A> *_self = _f._self;
          auto acc = std::move(_f.acc);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ptree<A>::PLeaf>(_sv.v())) {
            _result = std::move(acc);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(_after_pfold_in_PNode{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0), std::move(acc)});
          }
        } else {
          auto _f = std::move(std::get<_after_pfold_in_PNode>(_popped));
          _stack.pop_back();
          auto a1 = std::move(_f.a1);
          const ptree<A> &a2 = *_f.a2;
          _stack.emplace_back(_call{_f.a2, f(std::move(_result), a1)});
        }
      }
      return _result;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    ptree<T1> pmap(F0 &&f) const {
      const ptree<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of pmap: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const ptree<A> *_self;
      };

      struct _after_pmap_in_PNode {
        A a1;
        const ptree<A> *a2;
      };

      struct _after_pmap_in_PNode_2 {
        A a1;
        ptree<T1> _tmp2;
      };

      using _frame =
          std::variant<_call, _after_pmap_in_PNode, _after_pmap_in_PNode_2>;
      ptree<T1> _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const ptree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ptree<A>::PLeaf>(_sv.v())) {
            _result = ptree<T1>::pleaf();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(_after_pmap_in_PNode{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_pmap_in_PNode>(_popped)) {
          auto _f = std::move(std::get<_after_pmap_in_PNode>(_popped));
          _stack.pop_back();
          auto a1 = std::move(_f.a1);
          const ptree<A> &a2 = *_f.a2;
          _stack.emplace_back(
              _after_pmap_in_PNode_2{std::move(a1), std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_pmap_in_PNode_2>(_popped));
          _stack.pop_back();
          auto a1 = std::move(_f.a1);
          _result =
              ptree<T1>::pnode(std::move(_f._tmp2), f(a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 ptree_rec(T1 f, F1 &&f0) const {
      return this->template ptree_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 ptree_rect(T1 f, F1 &&f0) const {
      const ptree<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of ptree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const ptree<A> *_self;
      };

      struct _after_ptree_rect_in_PNode {
        std::shared_ptr<ptree<A>> a0;
        A a1;
        const ptree<A> *a2;
      };

      struct _after_ptree_rect_in_PNode_2 {
        std::shared_ptr<ptree<A>> a0;
        A a1;
        const ptree<A> *a2;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_ptree_rect_in_PNode,
                                  _after_ptree_rect_in_PNode_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const ptree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ptree<A>::PLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(
                _after_ptree_rect_in_PNode{a0, a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_ptree_rect_in_PNode>(_popped)) {
          auto _f = std::move(std::get<_after_ptree_rect_in_PNode>(_popped));
          _stack.pop_back();
          std::shared_ptr<ptree<A>> a0 = std::move(_f.a0);
          auto a1 = std::move(_f.a1);
          const ptree<A> &a2 = *_f.a2;
          _stack.emplace_back(_after_ptree_rect_in_PNode_2{
              std::move(a0), std::move(a1), &a2, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_ptree_rect_in_PNode_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<ptree<A>> a0 = std::move(_f.a0);
          auto a1 = std::move(_f.a1);
          const ptree<A> &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct stream {
    // TYPES
    template <typename CraneS0 = stream> struct SCons_ {
      uint64_t a0;
      CraneS0 a1;
    };

    using SCons = SCons_<>;
    using variant_t = std::variant<SCons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    stream() {}

    explicit stream(SCons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream scons(uint64_t a0, stream a1) {
      return stream(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, a0, std::move(a1)));
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream lazy_(F &&thunk) {
      return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  template <typename a> using st = crane::fn<std::pair<a, uint64_t>(uint64_t)>;

  template <typename T1> static st<T1> sret(T1 a) {
    return [=, a = std::move(a)](uint64_t s) { return std::make_pair(a, s); };
  }

  template <typename _tcI0, typename T1, typename F1>
    requires Sz<_tcI0, T1>
  static String f2(const T1 &a20, F1 &&, const ptree<bool> &) {
    auto _once1 =
        ptree<uint64_t>::pnode(ptree<uint64_t>::pleaf(),
                               Sum<crane::obj, T1>::inr(a20),
                               ptree<uint64_t>::pleaf())
            .template pmap<uint64_t>([](Sum<tree,
                                            T1>) {
          return UINT64_C(0);
        })
            .template pfold<uint64_t>(
            [](uint64_t, uint64_t) { return UINT64_C(0); }, UINT64_C(0));
    return String::emptystring().substring(
        UINT64_C(0), (UINT64_C(4) ? _once1 % UINT64_C(4) : _once1));
  }

  static inline const uint64_t t_5 = []() {
    return []() {
      String w111 = f2<sz_nat, uint64_t>(
          UINT64_C(0), [](uint64_t) { return sret<pt>(pt{UINT64_C(0), true}); },
          ptree<bool>::pleaf());
      return ((w111.length() * UINT64_C(13)) + [&]() -> uint64_t {
        auto _cs = w111.get(UINT64_C(0));
        if (_cs.has_value()) {
          const Ascii &c = *_cs;
          return Ascii0::nat_of_ascii(c);
        } else {
          return UINT64_C(0);
        }
      }());
    }();
  }();
};

inline std::optional<Ascii> String::get(uint64_t n) const {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const String *_loop_self = this;
  uint64_t _loop_n = n;
  while (true) {
    auto &&_sv = *_loop_self;
    if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
      return std::optional<Ascii>();
    } else {
      const auto &[a0, a1] = std::get<typename String::String0>(_sv.v());
      if (_loop_n <= 0) {
        return std::make_optional<Ascii>(a0);
      } else {
        uint64_t n_ = _loop_n - 1;
        _loop_self = crane_raw(a1);
        _loop_n = n_;
      }
    }
  }
}

inline String String::substring(uint64_t n, uint64_t m) const {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<String> _root{};
  std::shared_ptr<String> *_write = nullptr;
  const String *_loop_self = this;
  uint64_t _loop_n = n;
  uint64_t _loop_m = m;
  while (true) {
    if (_loop_n <= 0) {
      if (_loop_m <= 0) {
        auto _value = String::emptystring();
        (_write ? *(*_write = std::make_shared<String>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t m_ = _loop_m - 1;
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
          auto _value = *_loop_self;
          (_write ? *(*_write = std::make_shared<String>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename String::String0>(_sv.v());
          auto _cell = typename String::String0(a0, nullptr);
          String &_node =
              (_write ? *(*_write = std::make_shared<String>(std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename String::String0>(_node.v_mut()).a1;
          _loop_self = crane_raw(a1);
          _loop_n = UINT64_C(0);
          _loop_m = m_;
          continue;
        }
      }
    } else {
      uint64_t n_ = _loop_n - 1;
      auto &&_sv0 = *_loop_self;
      if (std::holds_alternative<typename String::EmptyString>(_sv0.v())) {
        auto _value = *_loop_self;
        (_write ? *(*_write = std::make_shared<String>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[_, a10] = std::get<typename String::String0>(_sv0.v());
        _loop_self = crane_raw(a10);
        _loop_n = n_;
        continue;
      }
    }
  }
  return std::move(*_root);
}
