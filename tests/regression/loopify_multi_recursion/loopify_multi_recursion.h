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
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
          if (_alt->a3 && _alt->a3.use_count() == 1) {
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

    /// _Cont_QQuad: saves [a0, a1, a2, a3], resumes after recursive call, then
    /// processes rest.
    struct _Cont_QQuad {
      std::shared_ptr<quadtree> a0;
      const quadtree *a1;
      const quadtree *a2;
      const quadtree *a3;
    };

    /// _Cont_QQuad_1: saves [_tmp4, a0, a1, a2, a3], resumes after recursive
    /// call, then processes rest.
    struct _Cont_QQuad_1 {
      T1 _tmp4;
      std::shared_ptr<quadtree> a0;
      const quadtree *a1;
      const quadtree *a2;
      const quadtree *a3;
    };

    /// _Cont_QQuad_2: saves [_tmp3, _tmp4, a0, a1, a2, a3], resumes after
    /// recursive call, then processes rest.
    struct _Cont_QQuad_2 {
      T1 _tmp3;
      T1 _tmp4;
      std::shared_ptr<quadtree> a0;
      const quadtree *a1;
      const quadtree *a2;
      const quadtree *a3;
    };

    /// _Cont_QQuad_3: saves [_tmp2, _tmp3, _tmp4, a0, a1, a2, a3], resumes
    /// after recursive call, then processes rest.
    struct _Cont_QQuad_3 {
      T1 _tmp2;
      T1 _tmp3;
      T1 _tmp4;
      std::shared_ptr<quadtree> a0;
      const quadtree *a1;
      const quadtree *a2;
      const quadtree *a3;
    };

    using _Frame = std::variant<_Enter, _Cont_QQuad, _Cont_QQuad_1,
                                _Cont_QQuad_2, _Cont_QQuad_3>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&q});
    /// Loopified quadtree_rect: _Enter -> _Cont_QQuad -> _Cont_QQuad_1 ->
    /// _Cont_QQuad_2 -> _Cont_QQuad_3.
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
          _stack.emplace_back(
              _Cont_QQuad{a0, crane_raw(a1), crane_raw(a2), crane_raw(a3)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_QQuad>(_frame)) {
        auto _f = std::move(std::get<_Cont_QQuad>(_frame));
        std::shared_ptr<quadtree> a0 = std::move(_f.a0);
        const quadtree &a1 = *_f.a1;
        const quadtree &a2 = *_f.a2;
        const quadtree &a3 = *_f.a3;
        _stack.emplace_back(
            _Cont_QQuad_1{std::move(_result), std::move(a0), &a1, &a2, &a3});
        _stack.emplace_back(_Enter{&a1});
      } else if (std::holds_alternative<_Cont_QQuad_1>(_frame)) {
        auto _f = std::move(std::get<_Cont_QQuad_1>(_frame));
        std::shared_ptr<quadtree> a0 = std::move(_f.a0);
        const quadtree &a1 = *_f.a1;
        const quadtree &a2 = *_f.a2;
        const quadtree &a3 = *_f.a3;
        _stack.emplace_back(_Cont_QQuad_2{std::move(_result),
                                          std::move(_f._tmp4), std::move(a0),
                                          &a1, &a2, &a3});
        _stack.emplace_back(_Enter{&a2});
      } else if (std::holds_alternative<_Cont_QQuad_2>(_frame)) {
        auto _f = std::move(std::get<_Cont_QQuad_2>(_frame));
        std::shared_ptr<quadtree> a0 = std::move(_f.a0);
        const quadtree &a1 = *_f.a1;
        const quadtree &a2 = *_f.a2;
        const quadtree &a3 = *_f.a3;
        _stack.emplace_back(
            _Cont_QQuad_3{std::move(_result), std::move(_f._tmp3),
                          std::move(_f._tmp4), std::move(a0), &a1, &a2, &a3});
        _stack.emplace_back(_Enter{&a3});
      } else {
        auto _f = std::move(std::get<_Cont_QQuad_3>(_frame));
        std::shared_ptr<quadtree> a0 = std::move(_f.a0);
        const quadtree &a1 = *_f.a1;
        const quadtree &a2 = *_f.a2;
        const quadtree &a3 = *_f.a3;
        _result = f0(*a0, std::move(_f._tmp4), a1, std::move(_f._tmp3), a2,
                     std::move(_f._tmp2), a3, std::move(_result));
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

    /// _Cont_QQuad: saves [a0, a1, a2, a3], resumes after recursive call, then
    /// processes rest.
    struct _Cont_QQuad {
      std::shared_ptr<quadtree> a0;
      const quadtree *a1;
      const quadtree *a2;
      const quadtree *a3;
    };

    /// _Cont_QQuad_1: saves [_tmp4, a0, a1, a2, a3], resumes after recursive
    /// call, then processes rest.
    struct _Cont_QQuad_1 {
      T1 _tmp4;
      std::shared_ptr<quadtree> a0;
      const quadtree *a1;
      const quadtree *a2;
      const quadtree *a3;
    };

    /// _Cont_QQuad_2: saves [_tmp3, _tmp4, a0, a1, a2, a3], resumes after
    /// recursive call, then processes rest.
    struct _Cont_QQuad_2 {
      T1 _tmp3;
      T1 _tmp4;
      std::shared_ptr<quadtree> a0;
      const quadtree *a1;
      const quadtree *a2;
      const quadtree *a3;
    };

    /// _Cont_QQuad_3: saves [_tmp2, _tmp3, _tmp4, a0, a1, a2, a3], resumes
    /// after recursive call, then processes rest.
    struct _Cont_QQuad_3 {
      T1 _tmp2;
      T1 _tmp3;
      T1 _tmp4;
      std::shared_ptr<quadtree> a0;
      const quadtree *a1;
      const quadtree *a2;
      const quadtree *a3;
    };

    using _Frame = std::variant<_Enter, _Cont_QQuad, _Cont_QQuad_1,
                                _Cont_QQuad_2, _Cont_QQuad_3>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&q});
    /// Loopified quadtree_rec: _Enter -> _Cont_QQuad -> _Cont_QQuad_1 ->
    /// _Cont_QQuad_2 -> _Cont_QQuad_3.
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
          _stack.emplace_back(
              _Cont_QQuad{a0, crane_raw(a1), crane_raw(a2), crane_raw(a3)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_QQuad>(_frame)) {
        auto _f = std::move(std::get<_Cont_QQuad>(_frame));
        std::shared_ptr<quadtree> a0 = std::move(_f.a0);
        const quadtree &a1 = *_f.a1;
        const quadtree &a2 = *_f.a2;
        const quadtree &a3 = *_f.a3;
        _stack.emplace_back(
            _Cont_QQuad_1{std::move(_result), std::move(a0), &a1, &a2, &a3});
        _stack.emplace_back(_Enter{&a1});
      } else if (std::holds_alternative<_Cont_QQuad_1>(_frame)) {
        auto _f = std::move(std::get<_Cont_QQuad_1>(_frame));
        std::shared_ptr<quadtree> a0 = std::move(_f.a0);
        const quadtree &a1 = *_f.a1;
        const quadtree &a2 = *_f.a2;
        const quadtree &a3 = *_f.a3;
        _stack.emplace_back(_Cont_QQuad_2{std::move(_result),
                                          std::move(_f._tmp4), std::move(a0),
                                          &a1, &a2, &a3});
        _stack.emplace_back(_Enter{&a2});
      } else if (std::holds_alternative<_Cont_QQuad_2>(_frame)) {
        auto _f = std::move(std::get<_Cont_QQuad_2>(_frame));
        std::shared_ptr<quadtree> a0 = std::move(_f.a0);
        const quadtree &a1 = *_f.a1;
        const quadtree &a2 = *_f.a2;
        const quadtree &a3 = *_f.a3;
        _stack.emplace_back(
            _Cont_QQuad_3{std::move(_result), std::move(_f._tmp3),
                          std::move(_f._tmp4), std::move(a0), &a1, &a2, &a3});
        _stack.emplace_back(_Enter{&a3});
      } else {
        auto _f = std::move(std::get<_Cont_QQuad_3>(_frame));
        std::shared_ptr<quadtree> a0 = std::move(_f.a0);
        const quadtree &a1 = *_f.a1;
        const quadtree &a2 = *_f.a2;
        const quadtree &a3 = *_f.a3;
        _result = f0(*a0, std::move(_f._tmp4), a1, std::move(_f._tmp3), a2,
                     std::move(_f._tmp2), a3, std::move(_result));
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
