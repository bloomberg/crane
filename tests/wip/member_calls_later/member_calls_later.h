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
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
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

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

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
    crane::small_vector<std::shared_ptr<Tree>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Node>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
        if (_alt->a1) {
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
  Tree(Tree &&) noexcept = default;
  Tree &operator=(Tree &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat deeper() const {
    const Tree *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const Tree *_self;
    };

    /// _After_Node: saves [a0], dispatches next recursive call.
    struct _After_Node {
      Tree *a0;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      Nat _result;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    Nat _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified deeper: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const Tree *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename Tree::Leaf>(_sv.v())) {
          _result = Nat::o();
        } else {
          const auto &[a0, a1] = std::get<typename Tree::Node>(_sv.v());
          _stack.emplace_back(_After_Node{crane_raw(a0)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{std::move(_result)});
        _stack.emplace_back(_Enter{_f.a0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result =
            Nat::s(Helper::pick(std::move(_result), std::move(_f._result)));
      }
    }
    return _result;
  }
};

struct Helper {
  static Nat pick(Nat a, Nat b);
};

#endif // INCLUDED_MEMBER_CALLS_LATER
