#ifndef INCLUDED_ITREE_REIFIED
#define INCLUDED_ITREE_REIFIED

#include <any>
#include <crane_itree.h>
#include <memory>
#include <string>
#include <type_traits>
#include <variant>

using namespace std::string_literals;
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

struct ITreeReified {
  /// Pass-through: takes a reified itree and returns it unchanged.
  static void run_tree(std::shared_ptr<ITree<void>> t);
  /// Sequence two reified itrees.
  static void sequence_trees(const std::shared_ptr<ITree<void>> &t1,
                             std::shared_ptr<ITree<void>> t2);
  /// Direct mode (no itree params) should be unchanged.
  static std::shared_ptr<ITree<void>> test_direct();

  /// Traverse an itree E T, logging at every Tau and Vis node.
  /// The result lives in itree (ioE +' E) T: original effects on
  /// the right, logging effects (IO) on the left.
  template <typename T1 = void, typename T2, typename F0>
  static std::shared_ptr<ITree<T2>> with_logging_body(F0 &&rec,
                                                      const itreeF_t<T2> &ot) {
    if (std::holds_alternative<typename ITree<T2>::Ret>(ot)) {
      const auto &_itf = *std::get_if<typename ITree<T2>::Ret>(&ot);
      auto r = _itf.value;
      return ITree<T2>::ret(r);
    } else if (std::holds_alternative<typename ITree<T2>::Tau>(ot)) {
      const auto &_itf = *std::get_if<typename ITree<T2>::Tau>(&ot);
      auto t_ = _itf.next;
      return itree_vis(
          [&]() -> std::any {
            std::cout << "[tau]"s << '\n';
            return std::any{};
          },
          [=](const std::any) mutable {
            return [&]() {
              auto t = rec(t_);
              return ITree<decltype(t->run())>::tau(t);
            }();
          });
    } else {
      const auto &_itf = *std::get_if<typename ITree<T2>::Vis>(&ot);
      auto e = _itf.effect;
      auto k = _itf.cont;
      return itree_vis(
          [&]() -> std::any {
            std::cout << "[vis]"s << '\n';
            return std::any{};
          },
          [=](const std::any) mutable {
            return itree_vis(
                e, [=](const std::any x) mutable { return rec(k(x)); });
          });
    }
  }

  template <typename T1 = void, typename T2>
  static std::shared_ptr<ITree<T2>>
  with_logging(const std::shared_ptr<ITree<T2>> &t) {
    return with_logging_body<T1, T2>(with_logging<T1, T2>, t->observe());
  }

  /// A simple tree to instrument.
  static std::shared_ptr<ITree<void>> greet();
  /// Apply with_logging to greet, producing itree (ioE +' ioE) unit.
  static std::shared_ptr<ITree<void>> test_logging();
  /// ---- Main (auto-wrapper) ----
  static std::shared_ptr<ITree<void>> main();
};

#endif // INCLUDED_ITREE_REIFIED
