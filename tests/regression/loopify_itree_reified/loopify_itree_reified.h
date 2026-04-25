#ifndef INCLUDED_LOOPIFY_ITREE_REIFIED
#define INCLUDED_LOOPIFY_ITREE_REIFIED

#include <any>
#include <crane_itree.h>
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
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
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

struct LoopifyItreeReified {
  /// Consumer fixpoint: traverses an ITree with fuel. This is a regular
  /// fixpoint with recursion on fuel that processes reified ITrees. Should
  /// be loopified normally (nontail with _Enter/_Call frames).
  __attribute__((pure)) static unsigned int
  count_taus(const unsigned int &fuel,
             const std::shared_ptr<ITree<unsigned int>> &t);

  /// HOF-pattern cofixpoint body: identity traversal on ITrees. Takes the
  /// recursive function as a parameter rec instead of calling itself
  /// directly, following the standard reified ITree cofixpoint pattern.
  /// The guardedness checker unfolds this transparent definition to verify
  /// that recursive calls are under Tau/Vis constructors.
  template <typename T1, typename F0>
  static std::shared_ptr<ITree<T1>> pass_body(F0 &&rec,
                                              const itreeF_t<T1> &ot) {
    if (std::holds_alternative<typename ITree<T1>::Ret>(ot)) {
      const auto &_itf = *std::get_if<typename ITree<T1>::Ret>(&ot);
      auto r = _itf.value;
      return ITree<T1>::ret(r);
    } else if (std::holds_alternative<typename ITree<T1>::Tau>(ot)) {
      const auto &_itf = *std::get_if<typename ITree<T1>::Tau>(&ot);
      auto t_ = _itf.next;
      return [&]() {
        auto t = rec(t_);
        return ITree<decltype(t->run())>::tau(t);
      }();
    } else {
      const auto &_itf = *std::get_if<typename ITree<T1>::Vis>(&ot);
      auto e = _itf.effect;
      auto k = _itf.cont;
      return itree_vis(e, [=](const std::any x) mutable { return rec(k(x)); });
    }
  }

  /// HOF-pattern cofixpoint: identity traversal that passes through all
  /// ITree nodes unchanged. In reified mode, the cofixpoint passes itself
  /// as a function value to pass_body, not as a direct recursive call.
  /// Loopify classifies this as No_recursion (correct — ITree::run()
  /// handles iteration). Since itree is custom-extracted, cofix_wrap
  /// does not fire. The polymorphic type parameter {R} is needed so the
  /// translator generates a template function, ensuring the self-reference
  /// is a template instantiation expression.
  template <typename T1>
  static std::shared_ptr<ITree<T1>> pass(const std::shared_ptr<ITree<T1>> &t) {
    return pass_body<T1>(pass<T1>, t->observe());
  }

  static inline const unsigned int test_count =
      count_taus(100u, ITree<unsigned int>::ret(42u));
};

#endif // INCLUDED_LOOPIFY_ITREE_REIFIED
