#ifndef INCLUDED_LOOPIFY_MULTI_RECURSION
#define INCLUDED_LOOPIFY_MULTI_RECURSION

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct LoopifyMultiRecursion {
  static uint64_t mixed_arith_fuel(uint64_t fuel, uint64_t n);
  static uint64_t mixed_arith(uint64_t n);
  static bool bool_or_chain_fuel(uint64_t fuel, uint64_t n, uint64_t target);
  static uint64_t bool_or_chain(uint64_t n, uint64_t target);
  static bool bool_and_chain_fuel(uint64_t fuel, uint64_t n);
  static uint64_t bool_and_chain(uint64_t n);

  struct quadtree {
    // TYPES
    struct QLeaf {
      uint64_t a0;
    };

    struct QQuad {
      std::shared_ptr<quadtree> a0;
      std::shared_ptr<quadtree> a1;
      std::shared_ptr<quadtree> a2;
      std::shared_ptr<quadtree> a3;
    };

    using variant_t = std::variant<QLeaf, QQuad>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : v_(std::move(_v)) {}

    explicit quadtree(QQuad _v) : v_(std::move(_v)) {}

    static quadtree qleaf(uint64_t a0) { return quadtree(QLeaf{a0}); }

    static quadtree qquad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(QQuad{std::make_shared<quadtree>(std::move(a0)),
                            std::make_shared<quadtree>(std::move(a1)),
                            std::make_shared<quadtree>(std::move(a2)),
                            std::make_shared<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      std::vector<std::shared_ptr<quadtree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<QQuad>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
          if (_alt->a3) {
            _stack.push_back(std::move(_alt->a3));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &, T1 &,
                                   quadtree &, T1 &, quadtree &, T1 &>
  static T1
  quadtree_rect(F0 &&f, F1 &&f0,
                const quadtree &q) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const quadtree *q;
    };

    using _Frame = std::variant<_Enter>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&q});
    /// Loopified quadtree_rect: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      const quadtree &q = *_f.q;
      if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(q.v());
        _result = f(a0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::QQuad>(q.v());
        _result = f0(*a0, quadtree_rect<T1>(f, f0, *a0), *a1,
                     quadtree_rect<T1>(f, f0, *a1), *a2,
                     quadtree_rect<T1>(f, f0, *a2), *a3,
                     quadtree_rect<T1>(f, f0, *a3));
      }
    }
    return _result;
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &, T1 &,
                                   quadtree &, T1 &, quadtree &, T1 &>
  static T1
  quadtree_rec(F0 &&f, F1 &&f0,
               const quadtree &q) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const quadtree *q;
    };

    using _Frame = std::variant<_Enter>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&q});
    /// Loopified quadtree_rec: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      const quadtree &q = *_f.q;
      if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
        const auto &[a0] = std::get<typename quadtree::QLeaf>(q.v());
        _result = f(a0);
      } else {
        const auto &[a0, a1, a2, a3] =
            std::get<typename quadtree::QQuad>(q.v());
        _result =
            f0(*a0, quadtree_rec<T1>(f, f0, *a0), *a1,
               quadtree_rec<T1>(f, f0, *a1), *a2, quadtree_rec<T1>(f, f0, *a2),
               *a3, quadtree_rec<T1>(f, f0, *a3));
      }
    }
    return _result;
  }

  static uint64_t quad_count_leaves(const quadtree &t);
  static uint64_t quad_depth(const quadtree &t);
  static uint64_t hofstadter_q_fuel(uint64_t fuel, uint64_t n);
  static uint64_t hofstadter_q(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_MULTI_RECURSION
