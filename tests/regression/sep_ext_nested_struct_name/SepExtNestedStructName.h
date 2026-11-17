#ifndef INCLUDED_SEPEXTNESTEDSTRUCTNAME
#define INCLUDED_SEPEXTNESTEDSTRUCTNAME

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

#include "NestedLib.h"

namespace SepExtNestedStructName {
struct Tree;

struct Tree {
  // TYPES
  struct Leaf {};

  struct Node {
    std::shared_ptr<Tree> a0;
    uint64_t a1;
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

  static Tree node(crane::shared_child_slot<Tree> a0, uint64_t a1) {
    return Tree(Node{a0.take(), a1});
  }

  // MANIPULATORS
  ~Tree() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Tree> {
      if (auto *_alt = std::get_if<Node>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Tree> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Tree(const Tree &) = default;
  Tree &operator=(const Tree &) = default;
  Tree(Tree &&) = default;
  Tree &operator=(Tree &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t depth() const {
    const Tree *_self = this;

    // Explicit stack replaces the non-tail recursion of depth: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const Tree *_self;
    };

    struct _after_depth_in_Node {};

    using _frame = std::variant<_call, _after_depth_in_Node>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const Tree *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename Tree::Leaf>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, _] = std::get<typename Tree::Node>(_sv.v());
          _stack.emplace_back(_after_depth_in_Node{});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_after_depth_in_Node>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

[[gnu::used]] inline const Tree sample =
    Tree::node(Tree::node(Tree::leaf(), UINT64_C(1)), UINT64_C(2));
const uint64_t total =
    (sample.depth() + NestedLib::Sub::size(NestedLib::Sub::Tree::node(
                          NestedLib::Sub::Tree::leaf(), UINT64_C(0),
                          NestedLib::Sub::Tree::leaf())));
} // namespace SepExtNestedStructName

#endif // INCLUDED_SEPEXTNESTEDSTRUCTNAME
