#ifndef INCLUDED_LOOPIFY_MULTI_RECURSION
#define INCLUDED_LOOPIFY_MULTI_RECURSION

#include "crane_fn.h"
#include "small_vector.h"
#include <algorithm>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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
      crane::small_vector<std::shared_ptr<quadtree>> _stack = {};
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
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    quadtree(const quadtree &) = default;
    quadtree &operator=(const quadtree &) = default;
    quadtree(quadtree &&) noexcept = default;
    quadtree &operator=(quadtree &&) noexcept = default;

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

    /// _After_QQuad: saves [a2_0, a1_0, a0_0, a3, a2_1, a1_1, a0_1], dispatches
    /// next recursive call.
    struct _After_QQuad {
      const quadtree *a2_0;
      const quadtree *a1_0;
      const quadtree *a0_0;
      quadtree a3;
      quadtree a2_1;
      quadtree a1_1;
      quadtree a0_1;
    };

    /// _After_QQuad_1: saves [_result, a1_0, a0_0, a3, a2, a1_1, a0_1],
    /// dispatches next recursive call.
    struct _After_QQuad_1 {
      std::decay_t<T1> _result;
      const quadtree *a1_0;
      const quadtree *a0_0;
      quadtree a3;
      quadtree a2;
      quadtree a1_1;
      quadtree a0_1;
    };

    /// _After_QQuad_2: saves [_result_0, _result_1, a0_0, a3, a2, a1, a0_1],
    /// dispatches next recursive call.
    struct _After_QQuad_2 {
      std::decay_t<T1> _result_0;
      std::decay_t<T1> _result_1;
      const quadtree *a0_0;
      quadtree a3;
      quadtree a2;
      quadtree a1;
      quadtree a0_1;
    };

    /// _Combine_QQuad: receives partial results, combines with _result from
    /// final call.
    struct _Combine_QQuad {
      std::decay_t<T1> _result_0;
      std::decay_t<T1> _result_1;
      std::decay_t<T1> _result_2;
      quadtree a3;
      quadtree a2;
      quadtree a1;
      quadtree a0;
    };

    using _Frame = std::variant<_Enter, _After_QQuad, _After_QQuad_1,
                                _After_QQuad_2, _Combine_QQuad>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&q});
    /// Loopified quadtree_rect: _Enter -> _After_QQuad -> _After_QQuad_1 ->
    /// _After_QQuad_2 -> _Combine_QQuad.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const quadtree &q = *_f.q;
        if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
          const auto &[a0] = std::get<typename quadtree::QLeaf>(q.v());
          _result = f(a0);
        } else {
          const auto &[a0, a1, a2, a3] =
              std::get<typename quadtree::QQuad>(q.v());
          _stack.emplace_back(_After_QQuad{crane_raw(a2), crane_raw(a1),
                                           crane_raw(a0), *a3, *a2, *a1, *a0});
          _stack.emplace_back(_Enter{crane_raw(a3)});
        }
      } else if (std::holds_alternative<_After_QQuad>(_frame)) {
        auto _f = std::move(std::get<_After_QQuad>(_frame));
        _stack.emplace_back(_After_QQuad_1{
            std::move(_result), _f.a1_0, _f.a0_0, std::move(_f.a3),
            std::move(_f.a2_1), std::move(_f.a1_1), std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a2_0});
      } else if (std::holds_alternative<_After_QQuad_1>(_frame)) {
        auto _f = std::move(std::get<_After_QQuad_1>(_frame));
        _stack.emplace_back(
            _After_QQuad_2{std::move(_f._result), std::move(_result), _f.a0_0,
                           std::move(_f.a3), std::move(_f.a2),
                           std::move(_f.a1_1), std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a1_0});
      } else if (std::holds_alternative<_After_QQuad_2>(_frame)) {
        auto _f = std::move(std::get<_After_QQuad_2>(_frame));
        _stack.emplace_back(_Combine_QQuad{
            std::move(_f._result_0), std::move(_f._result_1),
            std::move(_result), std::move(_f.a3), std::move(_f.a2),
            std::move(_f.a1), std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_QQuad>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                     std::move(_f._result_2), std::move(_f.a2),
                     std::move(_f._result_1), std::move(_f.a3),
                     std::move(_f._result_0));
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

    /// _After_QQuad: saves [a2_0, a1_0, a0_0, a3, a2_1, a1_1, a0_1], dispatches
    /// next recursive call.
    struct _After_QQuad {
      const quadtree *a2_0;
      const quadtree *a1_0;
      const quadtree *a0_0;
      quadtree a3;
      quadtree a2_1;
      quadtree a1_1;
      quadtree a0_1;
    };

    /// _After_QQuad_1: saves [_result, a1_0, a0_0, a3, a2, a1_1, a0_1],
    /// dispatches next recursive call.
    struct _After_QQuad_1 {
      std::decay_t<T1> _result;
      const quadtree *a1_0;
      const quadtree *a0_0;
      quadtree a3;
      quadtree a2;
      quadtree a1_1;
      quadtree a0_1;
    };

    /// _After_QQuad_2: saves [_result_0, _result_1, a0_0, a3, a2, a1, a0_1],
    /// dispatches next recursive call.
    struct _After_QQuad_2 {
      std::decay_t<T1> _result_0;
      std::decay_t<T1> _result_1;
      const quadtree *a0_0;
      quadtree a3;
      quadtree a2;
      quadtree a1;
      quadtree a0_1;
    };

    /// _Combine_QQuad: receives partial results, combines with _result from
    /// final call.
    struct _Combine_QQuad {
      std::decay_t<T1> _result_0;
      std::decay_t<T1> _result_1;
      std::decay_t<T1> _result_2;
      quadtree a3;
      quadtree a2;
      quadtree a1;
      quadtree a0;
    };

    using _Frame = std::variant<_Enter, _After_QQuad, _After_QQuad_1,
                                _After_QQuad_2, _Combine_QQuad>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&q});
    /// Loopified quadtree_rec: _Enter -> _After_QQuad -> _After_QQuad_1 ->
    /// _After_QQuad_2 -> _Combine_QQuad.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const quadtree &q = *_f.q;
        if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
          const auto &[a0] = std::get<typename quadtree::QLeaf>(q.v());
          _result = f(a0);
        } else {
          const auto &[a0, a1, a2, a3] =
              std::get<typename quadtree::QQuad>(q.v());
          _stack.emplace_back(_After_QQuad{crane_raw(a2), crane_raw(a1),
                                           crane_raw(a0), *a3, *a2, *a1, *a0});
          _stack.emplace_back(_Enter{crane_raw(a3)});
        }
      } else if (std::holds_alternative<_After_QQuad>(_frame)) {
        auto _f = std::move(std::get<_After_QQuad>(_frame));
        _stack.emplace_back(_After_QQuad_1{
            std::move(_result), _f.a1_0, _f.a0_0, std::move(_f.a3),
            std::move(_f.a2_1), std::move(_f.a1_1), std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a2_0});
      } else if (std::holds_alternative<_After_QQuad_1>(_frame)) {
        auto _f = std::move(std::get<_After_QQuad_1>(_frame));
        _stack.emplace_back(
            _After_QQuad_2{std::move(_f._result), std::move(_result), _f.a0_0,
                           std::move(_f.a3), std::move(_f.a2),
                           std::move(_f.a1_1), std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a1_0});
      } else if (std::holds_alternative<_After_QQuad_2>(_frame)) {
        auto _f = std::move(std::get<_After_QQuad_2>(_frame));
        _stack.emplace_back(_Combine_QQuad{
            std::move(_f._result_0), std::move(_f._result_1),
            std::move(_result), std::move(_f.a3), std::move(_f.a2),
            std::move(_f.a1), std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_QQuad>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                     std::move(_f._result_2), std::move(_f.a2),
                     std::move(_f._result_1), std::move(_f.a3),
                     std::move(_f._result_0));
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
