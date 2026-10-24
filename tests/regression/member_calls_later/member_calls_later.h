#ifndef INCLUDED_MEMBER_CALLS_LATER
#define INCLUDED_MEMBER_CALLS_LATER

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct Tree;

struct Helper {
  static Nat pick(Nat a, Nat b);
};

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct PeanoNat {
  static bool leb(const Nat &n, const Nat &m);
};

struct Tree {
  // TYPES
  struct Leaf {};

  struct Node {
    std::shared_ptr<Tree> a0;
    std::shared_ptr<Tree> a1;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Tree() {}

  explicit Tree(Leaf _v) : v_(_v) {}

  explicit Tree(Node _v) : v_(std::move(_v)) {}

  static Tree leaf() { return Tree(Leaf{}); }

  static Tree node(Tree a0, Tree a1) {
    return Tree(Node{std::make_shared<Tree>(std::move(a0)),
                     std::make_shared<Tree>(std::move(a1))});
  }

  // MANIPULATORS
  ~Tree() {
    if (std::holds_alternative<Leaf>(v_mut())) {
      return;
    }
    if (auto *_alt = std::get_if<Node>(&v_mut())) {
      if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
            (_alt->a1 && _alt->a1.use_count() == 1))) {
        return;
      }
    }
    crane::small_vector<std::shared_ptr<Tree>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Node>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          _stack.push_back(std::move(_alt->a0));
        }
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          _stack.push_back(std::move(_alt->a1));
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

  Tree(const Tree &) = default;
  Tree &operator=(const Tree &) = default;
  Tree(Tree &&) = default;
  Tree &operator=(Tree &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat deeper() const;
};

inline Nat Tree::deeper() const {
  const Tree *_self = this;

  /// CraneEnter: captures varying parameters for each recursive call.
  struct CraneEnter {
    const Tree *_self;
  };

  /// CraneCont_Node: saves [a1], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    const Tree *a1;
  };

  /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    Nat _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  Nat _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{_self});
  /// Loopified deeper: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const Tree *_self = _f._self;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename Tree::Leaf>(_sv.v())) {
        _result = Nat::o();
      } else {
        const auto &[a0, a1] = std::get<typename Tree::Node>(_sv.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(a1)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const Tree &a1 = *_f.a1;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{_f.a1});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = Nat::s(Helper::pick(std::move(_f._tmp2), std::move(_result)));
    }
  }
  return _result;
}

#endif // INCLUDED_MEMBER_CALLS_LATER
