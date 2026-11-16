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

  static Tree node(Tree a0, uint64_t a1) {
    return Tree(Node{std::make_shared<Tree>(std::move(a0)), a1});
  }

  // MANIPULATORS
  ~Tree() {
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
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
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
