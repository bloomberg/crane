#ifndef INCLUDED_LOOPIFY_MULTI_RECURSION
#define INCLUDED_LOOPIFY_MULTI_RECURSION

#include <algorithm>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct LoopifyMultiRecursion {
  __attribute__((pure)) static unsigned int
  mixed_arith_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int mixed_arith(const unsigned int &n);
  __attribute__((pure)) static bool
  bool_or_chain_fuel(const unsigned int &fuel, const unsigned int &n,
                     const unsigned int &target);
  __attribute__((pure)) static unsigned int
  bool_or_chain(const unsigned int &n, const unsigned int &target);
  __attribute__((pure)) static bool
  bool_and_chain_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int
  bool_and_chain(const unsigned int &n);

  struct quadtree {
    // TYPES
    struct QLeaf {
      unsigned int d_a0;
    };

    struct QQuad {
      std::unique_ptr<quadtree> d_a0;
      std::unique_ptr<quadtree> d_a1;
      std::unique_ptr<quadtree> d_a2;
      std::unique_ptr<quadtree> d_a3;
    };

    using variant_t = std::variant<QLeaf, QQuad>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : d_v_(std::move(_v)) {}

    explicit quadtree(QQuad _v) : d_v_(std::move(_v)) {}

    quadtree(const quadtree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    quadtree(quadtree &&_other) : d_v_(std::move(_other.d_v_)) {}

    quadtree &operator=(const quadtree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    quadtree &operator=(quadtree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) quadtree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<QLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<QLeaf>(_sv.v());
        return quadtree(QLeaf{d_a0});
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] = std::get<QQuad>(_sv.v());
        return quadtree(
            QQuad{d_a0 ? std::make_unique<LoopifyMultiRecursion::quadtree>(
                             d_a0->clone())
                       : nullptr,
                  d_a1 ? std::make_unique<LoopifyMultiRecursion::quadtree>(
                             d_a1->clone())
                       : nullptr,
                  d_a2 ? std::make_unique<LoopifyMultiRecursion::quadtree>(
                             d_a2->clone())
                       : nullptr,
                  d_a3 ? std::make_unique<LoopifyMultiRecursion::quadtree>(
                             d_a3->clone())
                       : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static quadtree qleaf(unsigned int a0) {
      return quadtree(QLeaf{std::move(a0)});
    }

    __attribute__((pure)) static quadtree qquad(quadtree a0, quadtree a1,
                                                quadtree a2, quadtree a3) {
      return quadtree(QQuad{std::make_unique<quadtree>(std::move(a0)),
                            std::make_unique<quadtree>(std::move(a1)),
                            std::make_unique<quadtree>(std::move(a2)),
                            std::make_unique<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      std::vector<std::unique_ptr<quadtree>> _stack;
      auto _drain = [&](quadtree &_node) {
        if (std::holds_alternative<QQuad>(_node.d_v_)) {
          auto &_alt = std::get<QQuad>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
          if (_alt.d_a2)
            _stack.push_back(std::move(_alt.d_a2));
          if (_alt.d_a3)
            _stack.push_back(std::move(_alt.d_a3));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, quadtree, T1, quadtree, T1, quadtree, T1, quadtree, T1> F1>
  static T1 quadtree_rect(F0 &&f, F1 &&f0, const quadtree &q) {
    if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
      const auto &[d_a0] = std::get<typename quadtree::QLeaf>(q.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1, d_a2, d_a3] =
          std::get<typename quadtree::QQuad>(q.v());
      return f0(*(d_a0), quadtree_rect<T1>(f, f0, *(d_a0)), *(d_a1),
                quadtree_rect<T1>(f, f0, *(d_a1)), *(d_a2),
                quadtree_rect<T1>(f, f0, *(d_a2)), *(d_a3),
                quadtree_rect<T1>(f, f0, *(d_a3)));
    }
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, quadtree, T1, quadtree, T1, quadtree, T1, quadtree, T1> F1>
  static T1 quadtree_rec(F0 &&f, F1 &&f0, const quadtree &q) {
    if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
      const auto &[d_a0] = std::get<typename quadtree::QLeaf>(q.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1, d_a2, d_a3] =
          std::get<typename quadtree::QQuad>(q.v());
      return f0(*(d_a0), quadtree_rec<T1>(f, f0, *(d_a0)), *(d_a1),
                quadtree_rec<T1>(f, f0, *(d_a1)), *(d_a2),
                quadtree_rec<T1>(f, f0, *(d_a2)), *(d_a3),
                quadtree_rec<T1>(f, f0, *(d_a3)));
    }
  }

  __attribute__((pure)) static unsigned int
  quad_count_leaves(const quadtree &t);
  __attribute__((pure)) static unsigned int quad_depth(const quadtree &t);
  __attribute__((pure)) static unsigned int
  hofstadter_q_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int hofstadter_q(const unsigned int &n);
};

#endif // INCLUDED_LOOPIFY_MULTI_RECURSION
