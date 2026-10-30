#ifndef INCLUDED_LOOPIFY_OPERAND_MATCH_CALL
#define INCLUDED_LOOPIFY_OPERAND_MATCH_CALL

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

struct LoopifyOperandMatchCall {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> l;
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

    static tree node(tree l, tree r) {
      return tree(Node{std::make_shared<tree>(std::move(l)),
                       std::make_shared<tree>(std::move(r))});
    }

    // MANIPULATORS
    ~tree() {
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
  static T1 tree_rect(T1 f, F1 &&f0,
                      const tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      const tree *t;
    };

    /// CraneCont_Node: saves [l0, r0], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node {
      std::shared_ptr<tree> l0;
      const tree *r0;
    };

    /// CraneCont_Node_1: saves [l0, r0, _tmp2], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_Node_1 {
      std::shared_ptr<tree> l0;
      const tree *r0;
      T1 _tmp2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&t});
    /// Loopified tree_rect: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[l0, r0] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(CraneCont_Node{l0, crane_raw(r0)});
          _stack.emplace_back(CraneEnter{crane_raw(l0)});
        }
      } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
        std::shared_ptr<tree> l0 = std::move(_f.l0);
        const tree &r0 = *_f.r0;
        _stack.emplace_back(
            CraneCont_Node_1{std::move(l0), &r0, std::move(_result)});
        _stack.emplace_back(CraneEnter{&r0});
      } else {
        auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
        std::shared_ptr<tree> l0 = std::move(_f.l0);
        const tree &r0 = *_f.r0;
        _result = f0(*l0, std::move(_f._tmp2), r0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(std::move(f), f0, t);
  }

  static uint64_t depthish(const tree &t);
  static tree mirror(const tree &t);
  static uint64_t size(const tree &t);
  static tree comb(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_OPERAND_MATCH_CALL
