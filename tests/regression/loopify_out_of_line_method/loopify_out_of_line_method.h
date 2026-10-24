#ifndef INCLUDED_LOOPIFY_OUT_OF_LINE_METHOD
#define INCLUDED_LOOPIFY_OUT_OF_LINE_METHOD

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

struct Tree;
struct Forest;
/// A method its struct only declares, defined after the struct, is
/// loopified as one defined inside it.
/// tree and forest are a mutual group at the top level, so a member
/// naming a struct of the group is written after the whole group: depth,
/// a method of tree, is declared in Tree and defined after it.  Loopify
/// transformed the methods it found in the struct and never looked at a
/// definition written out of line, so depth kept recursing in C++, one
/// stack frame per node, though every other method of the struct was a
/// loop.  A million nodes overflow the stack without the fix.
struct tree;
struct forest;

struct Tree {
  // TYPES
  struct Leaf {};

  struct Node {
    std::shared_ptr<Forest> a0;
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

  static Tree leaf();
  static Tree node(Forest a0, Tree a1);
  // MANIPULATORS
  ~Tree();
  Tree(const Tree &) = default;
  Tree &operator=(const Tree &) = default;
  Tree(Tree &&) = default;
  Tree &operator=(Tree &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t depth() const;
};

struct Forest {
  // TYPES
  struct Bare {};

  struct Grove {
    std::shared_ptr<Tree> a0;
    std::shared_ptr<Forest> a1;
  };

  using variant_t = std::variant<Bare, Grove>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Forest() {}

  explicit Forest(Bare _v) : v_(_v) {}

  explicit Forest(Grove _v) : v_(std::move(_v)) {}

  static Forest bare();
  static Forest grove(Tree a0, Forest a1);
  // MANIPULATORS
  ~Forest();
  Forest(const Forest &) = default;
  Forest &operator=(const Forest &) = default;
  Forest(Forest &&) = default;
  Forest &operator=(Forest &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

inline Tree Tree::leaf() { return Tree(Leaf{}); }

inline Tree Tree::node(Forest a0, Tree a1) {
  return Tree(Node{std::make_shared<Forest>(std::move(a0)),
                   std::make_shared<Tree>(std::move(a1))});
}

inline Tree::~Tree() {
  crane::small_vector<crane::obj> _stack = {};
  auto _drain_self = [&](variant_t &_v) {
    if (auto *_alt = std::get_if<Node>(&_v)) {
      if (_alt->a0 && _alt->a0.use_count() == 1) {
        _stack.push_back(std::move(_alt->a0));
      }
      if (_alt->a1 && _alt->a1.use_count() == 1) {
        _stack.push_back(std::move(_alt->a1));
      }
    }
  };
  _drain_self(v_mut());
  while (!_stack.empty()) {
    auto _cur = std::move(_stack.back());
    _stack.pop_back();
    if (auto *_sp = crane::any_cast<std::shared_ptr<Tree>>(&_cur)) {
      if (*_sp && (*_sp).use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain_self((*_sp)->v_mut());
      }
    } else {
      if (auto *_sp = crane::any_cast<std::shared_ptr<Forest>>(&_cur)) {
        if (*_sp && (*_sp).use_count() == 1) {
          auto &_pv = (*_sp)->v_mut();
          if (auto *_alt = std::get_if<typename Forest::Grove>(&_pv)) {
            if (_alt->a0 && _alt->a0.use_count() == 1) {
              _stack.push_back(std::move(_alt->a0));
            }
            if (_alt->a1 && _alt->a1.use_count() == 1) {
              _stack.push_back(std::move(_alt->a1));
            }
          }
        }
      }
    }
  }
}

inline uint64_t Tree::depth() const {
  const Tree *_self = this;

  /// CraneEnter: captures varying parameters for each recursive call.
  struct CraneEnter {
    const Tree *_self;
  };

  /// CraneCont_Node: resumes after recursive call, then processes rest.
  struct CraneCont_Node {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{_self});
  /// Loopified depth: CraneEnter -> CraneCont_Node.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const Tree *_self = _f._self;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename Tree::Leaf>(_sv.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename Tree::Node>(_sv.v());
        _stack.emplace_back(CraneCont_Node{});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      _result = (std::move(_result) + UINT64_C(1));
    }
  }
  return _result;
}

inline Forest Forest::bare() { return Forest(Bare{}); }

inline Forest Forest::grove(Tree a0, Forest a1) {
  return Forest(Grove{std::make_shared<Tree>(std::move(a0)),
                      std::make_shared<Forest>(std::move(a1))});
}

inline Forest::~Forest() {
  crane::small_vector<crane::obj> _stack = {};
  auto _drain_self = [&](variant_t &_v) {
    if (auto *_alt = std::get_if<Grove>(&_v)) {
      if (_alt->a0 && _alt->a0.use_count() == 1) {
        _stack.push_back(std::move(_alt->a0));
      }
      if (_alt->a1 && _alt->a1.use_count() == 1) {
        _stack.push_back(std::move(_alt->a1));
      }
    }
  };
  _drain_self(v_mut());
  while (!_stack.empty()) {
    auto _cur = std::move(_stack.back());
    _stack.pop_back();
    if (auto *_sp = crane::any_cast<std::shared_ptr<Forest>>(&_cur)) {
      if (*_sp && (*_sp).use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain_self((*_sp)->v_mut());
      }
    } else {
      if (auto *_sp = crane::any_cast<std::shared_ptr<Tree>>(&_cur)) {
        if (*_sp && (*_sp).use_count() == 1) {
          auto &_pv = (*_sp)->v_mut();
          if (auto *_alt = std::get_if<typename Tree::Node>(&_pv)) {
            if (_alt->a0 && _alt->a0.use_count() == 1) {
              _stack.push_back(std::move(_alt->a0));
            }
            if (_alt->a1 && _alt->a1.use_count() == 1) {
              _stack.push_back(std::move(_alt->a1));
            }
          }
        }
      }
    }
  }
}

#endif // INCLUDED_LOOPIFY_OUT_OF_LINE_METHOD
