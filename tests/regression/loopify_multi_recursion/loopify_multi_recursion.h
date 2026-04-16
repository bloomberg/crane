#ifndef INCLUDED_LOOPIFY_MULTI_RECURSION
#define INCLUDED_LOOPIFY_MULTI_RECURSION

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct LoopifyMultiRecursion {
  __attribute__((pure)) static unsigned int
  mixed_arith_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int mixed_arith(const unsigned int n);
  __attribute__((pure)) static bool
  bool_or_chain_fuel(const unsigned int fuel, const unsigned int n,
                     const unsigned int target);
  __attribute__((pure)) static unsigned int
  bool_or_chain(const unsigned int n, const unsigned int target);
  __attribute__((pure)) static bool bool_and_chain_fuel(const unsigned int fuel,
                                                        const unsigned int n);
  __attribute__((pure)) static unsigned int
  bool_and_chain(const unsigned int n);

  struct quadtree {
    // TYPES
    struct QLeaf {
      unsigned int d_a0;
    };

    struct QQuad {
      std::shared_ptr<quadtree> d_a0;
      std::shared_ptr<quadtree> d_a1;
      std::shared_ptr<quadtree> d_a2;
      std::shared_ptr<quadtree> d_a3;
    };

    using variant_t = std::variant<QLeaf, QQuad>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit quadtree(QLeaf _v) : d_v_(std::move(_v)) {}

    explicit quadtree(QQuad _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<quadtree> qleaf(unsigned int a0) {
      return std::make_shared<quadtree>(QLeaf{std::move(a0)});
    }

    static std::shared_ptr<quadtree>
    qquad(const std::shared_ptr<quadtree> &a0,
          const std::shared_ptr<quadtree> &a1,
          const std::shared_ptr<quadtree> &a2,
          const std::shared_ptr<quadtree> &a3) {
      return std::make_shared<quadtree>(QQuad{a0, a1, a2, a3});
    }

    static std::shared_ptr<quadtree> qquad(std::shared_ptr<quadtree> &&a0,
                                           std::shared_ptr<quadtree> &&a1,
                                           std::shared_ptr<quadtree> &&a2,
                                           std::shared_ptr<quadtree> &&a3) {
      return std::make_shared<quadtree>(
          QQuad{std::move(a0), std::move(a1), std::move(a2), std::move(a3)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1,
             std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1>
          F1>
  static T1 quadtree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<quadtree> &q) {
    struct _Enter {
      const std::shared_ptr<quadtree> q;
    };

    struct _Call1 {
      const std::shared_ptr<quadtree> _s0;
      const std::shared_ptr<quadtree> _s1;
      const std::shared_ptr<quadtree> _s2;
      std::shared_ptr<quadtree> _s3;
      std::shared_ptr<quadtree> _s4;
      std::shared_ptr<quadtree> _s5;
      std::shared_ptr<quadtree> _s6;
    };

    struct _Call2 {
      T1 _s0;
      const std::shared_ptr<quadtree> _s1;
      const std::shared_ptr<quadtree> _s2;
      std::shared_ptr<quadtree> _s3;
      std::shared_ptr<quadtree> _s4;
      std::shared_ptr<quadtree> _s5;
      std::shared_ptr<quadtree> _s6;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      const std::shared_ptr<quadtree> _s2;
      std::shared_ptr<quadtree> _s3;
      std::shared_ptr<quadtree> _s4;
      std::shared_ptr<quadtree> _s5;
      std::shared_ptr<quadtree> _s6;
    };

    struct _Call4 {
      T1 _s0;
      T1 _s1;
      T1 _s2;
      std::shared_ptr<quadtree> _s3;
      std::shared_ptr<quadtree> _s4;
      std::shared_ptr<quadtree> _s5;
      std::shared_ptr<quadtree> _s6;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{q});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<quadtree> q = _f.q;
        if (std::holds_alternative<typename quadtree::QLeaf>(q->v())) {
          const auto &[d_a0] = std::get<typename quadtree::QLeaf>(q->v());
          _result = f(d_a0);
        } else {
          const auto &[d_a0, d_a1, d_a2, d_a3] =
              std::get<typename quadtree::QQuad>(q->v());
          _stack.emplace_back(_Call1{d_a2, d_a1, d_a0, d_a3, d_a2, d_a1, d_a0});
          _stack.emplace_back(_Enter{d_a3});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        const auto &_f = std::get<_Call1>(_frame);
        _stack.emplace_back(
            _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s0});
      } else if (std::holds_alternative<_Call2>(_frame)) {
        const auto &_f = std::get<_Call2>(_frame);
        _stack.emplace_back(
            _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s1});
      } else if (std::holds_alternative<_Call3>(_frame)) {
        const auto &_f = std::get<_Call3>(_frame);
        _stack.emplace_back(
            _Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s2});
      } else {
        const auto &_f = std::get<_Call4>(_frame);
        _result =
            f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1, _f._s3, _f._s0);
      }
    }
    return _result;
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1,
             std::shared_ptr<quadtree>, T1, std::shared_ptr<quadtree>, T1>
          F1>
  static T1 quadtree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<quadtree> &q) {
    struct _Enter {
      const std::shared_ptr<quadtree> q;
    };

    struct _Call1 {
      const std::shared_ptr<quadtree> _s0;
      const std::shared_ptr<quadtree> _s1;
      const std::shared_ptr<quadtree> _s2;
      std::shared_ptr<quadtree> _s3;
      std::shared_ptr<quadtree> _s4;
      std::shared_ptr<quadtree> _s5;
      std::shared_ptr<quadtree> _s6;
    };

    struct _Call2 {
      T1 _s0;
      const std::shared_ptr<quadtree> _s1;
      const std::shared_ptr<quadtree> _s2;
      std::shared_ptr<quadtree> _s3;
      std::shared_ptr<quadtree> _s4;
      std::shared_ptr<quadtree> _s5;
      std::shared_ptr<quadtree> _s6;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      const std::shared_ptr<quadtree> _s2;
      std::shared_ptr<quadtree> _s3;
      std::shared_ptr<quadtree> _s4;
      std::shared_ptr<quadtree> _s5;
      std::shared_ptr<quadtree> _s6;
    };

    struct _Call4 {
      T1 _s0;
      T1 _s1;
      T1 _s2;
      std::shared_ptr<quadtree> _s3;
      std::shared_ptr<quadtree> _s4;
      std::shared_ptr<quadtree> _s5;
      std::shared_ptr<quadtree> _s6;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{q});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<quadtree> q = _f.q;
        if (std::holds_alternative<typename quadtree::QLeaf>(q->v())) {
          const auto &[d_a0] = std::get<typename quadtree::QLeaf>(q->v());
          _result = f(d_a0);
        } else {
          const auto &[d_a0, d_a1, d_a2, d_a3] =
              std::get<typename quadtree::QQuad>(q->v());
          _stack.emplace_back(_Call1{d_a2, d_a1, d_a0, d_a3, d_a2, d_a1, d_a0});
          _stack.emplace_back(_Enter{d_a3});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        const auto &_f = std::get<_Call1>(_frame);
        _stack.emplace_back(
            _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s0});
      } else if (std::holds_alternative<_Call2>(_frame)) {
        const auto &_f = std::get<_Call2>(_frame);
        _stack.emplace_back(
            _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s1});
      } else if (std::holds_alternative<_Call3>(_frame)) {
        const auto &_f = std::get<_Call3>(_frame);
        _stack.emplace_back(
            _Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s2});
      } else {
        const auto &_f = std::get<_Call4>(_frame);
        _result =
            f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1, _f._s3, _f._s0);
      }
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  quad_count_leaves(const std::shared_ptr<quadtree> &t);
  __attribute__((pure)) static unsigned int
  quad_depth(const std::shared_ptr<quadtree> &t);
  __attribute__((pure)) static unsigned int
  hofstadter_q_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int hofstadter_q(const unsigned int n);
};

#endif // INCLUDED_LOOPIFY_MULTI_RECURSION
