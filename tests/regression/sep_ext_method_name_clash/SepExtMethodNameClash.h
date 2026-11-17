#ifndef INCLUDED_SEPEXTMETHODNAMECLASH
#define INCLUDED_SEPEXTMETHODNAMECLASH

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

namespace SepExtMethodNameClash {
struct Tree;

struct Tree {
  // TYPES
  struct Leaf {};

  struct Node {
    std::shared_ptr<Tree> a0;
    uint64_t a1;
    std::shared_ptr<Tree> a2;
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

  static Tree node(Tree a0, uint64_t a1, Tree a2) {
    return Tree(Node{std::make_shared<Tree>(std::move(a0)), a1,
                     std::make_shared<Tree>(std::move(a2))});
  }

  // MANIPULATORS
  ~Tree() {
    if (std::holds_alternative<Leaf>(v_mut())) {
      return;
    }
    if (auto *_alt = std::get_if<Node>(&v_mut())) {
      if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
            (_alt->a2 && _alt->a2.use_count() == 1))) {
        return;
      }
    }
    crane::small_vector<std::shared_ptr<Tree>> _stack = {};
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

  Tree(const Tree &) = default;
  Tree &operator=(const Tree &) = default;
  Tree(Tree &&) = default;
  Tree &operator=(Tree &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t clone0() const {
    const Tree *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const Tree *_self;
    };

    /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node {
      uint64_t a1;
      const Tree *a2;
    };

    /// CraneCont_Node_1: saves [a1, _tmp2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node_1 {
      uint64_t a1;
      uint64_t _tmp2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified clone0: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
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
          const auto &[a0, a1, a2] = std::get<typename Tree::Node>(_sv.v());
          _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
        uint64_t a1 = _f.a1;
        const Tree &a2 = *_f.a2;
        _stack.emplace_back(CraneCont_Node_1{a1, std::move(_result)});
        _stack.emplace_back(CraneEnter{_f.a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
        uint64_t a1 = _f.a1;
        _result = ((_f._tmp2 + a1) + std::move(_result));
      }
    }
    return _result;
  }

  uint64_t leaf0() const {
    if (std::holds_alternative<typename Tree::Leaf>(this->v())) {
      return UINT64_C(1);
    } else {
      return UINT64_C(0);
    }
  }
};

[[gnu::used]] inline const Tree sample =
    Tree::node(Tree::node(Tree::leaf(), UINT64_C(1), Tree::leaf()), UINT64_C(2),
               Tree::node(Tree::leaf(), UINT64_C(3), Tree::leaf()));
const uint64_t total =
    ((sample.clone0() + sample.leaf0()) + Tree::leaf().leaf0());
} // namespace SepExtMethodNameClash

#endif // INCLUDED_SEPEXTMETHODNAMECLASH
