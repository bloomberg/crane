#ifndef INCLUDED_LOOPIFY_MULTI_RECURSION
#define INCLUDED_LOOPIFY_MULTI_RECURSION

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

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

    __attribute__((pure)) quadtree &operator=(const quadtree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) quadtree &operator=(quadtree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) quadtree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<QLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<QLeaf>(_sv.v());
        return quadtree(QLeaf{clone_as_value<unsigned int>(d_a0)});
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] = std::get<QQuad>(_sv.v());
        return quadtree(QQuad{clone_as_value<std::unique_ptr<quadtree>>(d_a0),
                              clone_as_value<std::unique_ptr<quadtree>>(d_a1),
                              clone_as_value<std::unique_ptr<quadtree>>(d_a2),
                              clone_as_value<std::unique_ptr<quadtree>>(d_a3)});
      }
    }

    // CREATORS
    __attribute__((pure)) static quadtree qleaf(unsigned int a0) {
      return quadtree(QLeaf{std::move(a0)});
    }

    __attribute__((pure)) static quadtree qquad(const quadtree &a0,
                                                const quadtree &a1,
                                                const quadtree &a2,
                                                const quadtree &a3) {
      return quadtree(QQuad{std::make_unique<quadtree>(a0.clone()),
                            std::make_unique<quadtree>(a1.clone()),
                            std::make_unique<quadtree>(a2.clone()),
                            std::make_unique<quadtree>(a3.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) quadtree *operator->() { return this; }

    __attribute__((pure)) const quadtree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = quadtree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, quadtree, T1, quadtree, T1, quadtree, T1, quadtree, T1> F1>
  static T1 quadtree_rect(F0 &&f, F1 &&f0, const quadtree &q) {
    struct _Enter {
      const quadtree q;
    };

    struct _Call1 {
      const quadtree _s0;
      const quadtree _s1;
      const quadtree _s2;
      quadtree _s3;
      quadtree _s4;
      quadtree _s5;
      quadtree _s6;
    };

    struct _Call2 {
      T1 _s0;
      const quadtree _s1;
      const quadtree _s2;
      quadtree _s3;
      quadtree _s4;
      quadtree _s5;
      quadtree _s6;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      const quadtree _s2;
      quadtree _s3;
      quadtree _s4;
      quadtree _s5;
      quadtree _s6;
    };

    struct _Call4 {
      T1 _s0;
      T1 _s1;
      T1 _s2;
      quadtree _s3;
      quadtree _s4;
      quadtree _s5;
      quadtree _s6;
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
        auto _f = std::move(std::get<_Enter>(_frame));
        const quadtree q = _f.q;
        if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
          const auto &[d_a0] = std::get<typename quadtree::QLeaf>(q.v());
          _result = f(d_a0);
        } else {
          const auto &[d_a0, d_a1, d_a2, d_a3] =
              std::get<typename quadtree::QQuad>(q.v());
          _stack.emplace_back(_Call1{*(d_a2), *(d_a1), *(d_a0), *(d_a3),
                                     *(d_a2), *(d_a1), *(d_a0)});
          _stack.emplace_back(_Enter{*(d_a3)});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        auto _f = std::move(std::get<_Call1>(_frame));
        _stack.emplace_back(
            _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s0});
      } else if (std::holds_alternative<_Call2>(_frame)) {
        auto _f = std::move(std::get<_Call2>(_frame));
        _stack.emplace_back(
            _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s1});
      } else if (std::holds_alternative<_Call3>(_frame)) {
        auto _f = std::move(std::get<_Call3>(_frame));
        _stack.emplace_back(
            _Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s2});
      } else {
        auto _f = std::move(std::get<_Call4>(_frame));
        _result =
            f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1, _f._s3, _f._s0);
      }
    }
    return _result;
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, quadtree, T1, quadtree, T1, quadtree, T1, quadtree, T1> F1>
  static T1 quadtree_rec(F0 &&f, F1 &&f0, const quadtree &q) {
    struct _Enter {
      const quadtree q;
    };

    struct _Call1 {
      const quadtree _s0;
      const quadtree _s1;
      const quadtree _s2;
      quadtree _s3;
      quadtree _s4;
      quadtree _s5;
      quadtree _s6;
    };

    struct _Call2 {
      T1 _s0;
      const quadtree _s1;
      const quadtree _s2;
      quadtree _s3;
      quadtree _s4;
      quadtree _s5;
      quadtree _s6;
    };

    struct _Call3 {
      T1 _s0;
      T1 _s1;
      const quadtree _s2;
      quadtree _s3;
      quadtree _s4;
      quadtree _s5;
      quadtree _s6;
    };

    struct _Call4 {
      T1 _s0;
      T1 _s1;
      T1 _s2;
      quadtree _s3;
      quadtree _s4;
      quadtree _s5;
      quadtree _s6;
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
        auto _f = std::move(std::get<_Enter>(_frame));
        const quadtree q = _f.q;
        if (std::holds_alternative<typename quadtree::QLeaf>(q.v())) {
          const auto &[d_a0] = std::get<typename quadtree::QLeaf>(q.v());
          _result = f(d_a0);
        } else {
          const auto &[d_a0, d_a1, d_a2, d_a3] =
              std::get<typename quadtree::QQuad>(q.v());
          _stack.emplace_back(_Call1{*(d_a2), *(d_a1), *(d_a0), *(d_a3),
                                     *(d_a2), *(d_a1), *(d_a0)});
          _stack.emplace_back(_Enter{*(d_a3)});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        auto _f = std::move(std::get<_Call1>(_frame));
        _stack.emplace_back(
            _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s0});
      } else if (std::holds_alternative<_Call2>(_frame)) {
        auto _f = std::move(std::get<_Call2>(_frame));
        _stack.emplace_back(
            _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s1});
      } else if (std::holds_alternative<_Call3>(_frame)) {
        auto _f = std::move(std::get<_Call3>(_frame));
        _stack.emplace_back(
            _Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4, _f._s5, _f._s6});
        _stack.emplace_back(_Enter{_f._s2});
      } else {
        auto _f = std::move(std::get<_Call4>(_frame));
        _result =
            f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1, _f._s3, _f._s0);
      }
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  quad_count_leaves(const quadtree &t);
  __attribute__((pure)) static unsigned int quad_depth(const quadtree &t);
  __attribute__((pure)) static unsigned int
  hofstadter_q_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int hofstadter_q(const unsigned int &n);
};

#endif // INCLUDED_LOOPIFY_MULTI_RECURSION
