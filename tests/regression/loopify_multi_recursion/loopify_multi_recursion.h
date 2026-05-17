#ifndef INCLUDED_LOOPIFY_MULTI_RECURSION
#define INCLUDED_LOOPIFY_MULTI_RECURSION

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct LoopifyMultiRecursion {
  static unsigned int mixed_arith_fuel(unsigned int fuel, unsigned int n);
  static unsigned int mixed_arith(unsigned int n);
  static bool bool_or_chain_fuel(unsigned int fuel, unsigned int n,
                                 unsigned int target);
  static unsigned int bool_or_chain(unsigned int n, unsigned int target);
  static bool bool_and_chain_fuel(unsigned int fuel, unsigned int n);
  static unsigned int bool_and_chain(unsigned int n);

  struct quadtree {
    // TYPES
    struct QLeaf {
      unsigned int a0;
    };

    struct QQuad {
      std::unique_ptr<quadtree> a0;
      std::unique_ptr<quadtree> a1;
      std::unique_ptr<quadtree> a2;
      std::unique_ptr<quadtree> a3;
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

    quadtree(const quadtree &_other) : v_(std::move(_other.clone().v_)) {}

    quadtree(quadtree &&_other) noexcept : v_(std::move(_other.v_)) {}

    quadtree &operator=(const quadtree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    quadtree &operator=(quadtree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    quadtree clone() const {
      quadtree _out{};

      struct _CloneFrame {
        const quadtree *_src;
        quadtree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const quadtree *_src = _frame._src;
        quadtree *_dst = _frame._dst;
        if (std::holds_alternative<QLeaf>(_src->v())) {
          const auto &_alt = std::get<QLeaf>(_src->v());
          _dst->v_ = QLeaf{_alt.a0};
        } else {
          const auto &_alt = std::get<QQuad>(_src->v());
          _dst->v_ = QQuad{_alt.a0 ? std::make_unique<quadtree>() : nullptr,
                           _alt.a1 ? std::make_unique<quadtree>() : nullptr,
                           _alt.a2 ? std::make_unique<quadtree>() : nullptr,
                           _alt.a3 ? std::make_unique<quadtree>() : nullptr};
          auto &_dst_alt = std::get<QQuad>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
          if (_alt.a3) {
            _stack.push_back({_alt.a3.get(), _dst_alt.a3.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static quadtree qleaf(unsigned int a0) { return quadtree(QLeaf{a0}); }

    static quadtree qquad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(QQuad{std::make_unique<quadtree>(std::move(a0)),
                            std::make_unique<quadtree>(std::move(a1)),
                            std::make_unique<quadtree>(std::move(a2)),
                            std::make_unique<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      std::vector<std::unique_ptr<quadtree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](quadtree &_node) {
        if (std::holds_alternative<QQuad>(_node.v_)) {
          auto &_alt = std::get<QQuad>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
          if (_alt.a3) {
            _stack.push_back(std::move(_alt.a3));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &, T1 &,
                                   quadtree &, T1 &, quadtree &, T1 &>
  static T1 quadtree_rect(F0 &&f, F1 &&f0, const quadtree &q) {
    if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
      const auto &[a0] = std::get<typename quadtree::QLeaf>(q.v());
      return f(a0);
    } else {
      const auto &[a0, a1, a2, a3] = std::get<typename quadtree::QQuad>(q.v());
      return f0(*a0, quadtree_rect<T1>(f, f0, *a0), *a1,
                quadtree_rect<T1>(f, f0, *a1), *a2,
                quadtree_rect<T1>(f, f0, *a2), *a3,
                quadtree_rect<T1>(f, f0, *a3));
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &, T1 &,
                                   quadtree &, T1 &, quadtree &, T1 &>
  static T1 quadtree_rec(F0 &&f, F1 &&f0, const quadtree &q) {
    if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
      const auto &[a0] = std::get<typename quadtree::QLeaf>(q.v());
      return f(a0);
    } else {
      const auto &[a0, a1, a2, a3] = std::get<typename quadtree::QQuad>(q.v());
      return f0(*a0, quadtree_rec<T1>(f, f0, *a0), *a1,
                quadtree_rec<T1>(f, f0, *a1), *a2, quadtree_rec<T1>(f, f0, *a2),
                *a3, quadtree_rec<T1>(f, f0, *a3));
    }
  }

  static unsigned int quad_count_leaves(const quadtree &t);
  static unsigned int quad_depth(const quadtree &t);
  static unsigned int hofstadter_q_fuel(unsigned int fuel, unsigned int n);
  static unsigned int hofstadter_q(unsigned int n);
};

#endif // INCLUDED_LOOPIFY_MULTI_RECURSION
