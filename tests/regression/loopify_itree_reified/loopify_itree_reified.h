#ifndef INCLUDED_LOOPIFY_ITREE_REIFIED
#define INCLUDED_LOOPIFY_ITREE_REIFIED

#include <any>
#include <crane_itree.h>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct LoopifyItreeReified {
  /// Consumer fixpoint: traverses an ITree with fuel. This is a regular
  /// fixpoint with recursion on fuel that processes reified ITrees. Should
  /// be loopified normally (nontail with _Enter/_Call frames).
  __attribute__((pure)) static unsigned int
  count_taus(const unsigned int fuel,
             const std::shared_ptr<ITree<unsigned int>> t);

  /// HOF-pattern cofixpoint body: identity traversal on ITrees. Takes the
  /// recursive function as a parameter rec instead of calling itself
  /// directly, following the standard reified ITree cofixpoint pattern.
  /// The guardedness checker unfolds this transparent definition to verify
  /// that recursive calls are under Tau/Vis constructors.
  template <typename T1, typename F0>
  static std::shared_ptr<ITree<T1>> pass_body(F0 &&rec, const itreeF_t<T1> ot) {
    return std::visit(
        Overloaded{[&](const typename ITree<T1>::Ret &_itf) -> decltype(auto) {
                     auto r = _itf.value;
                     return ITree<T1>::ret(r);
                   },
                   [&](const typename ITree<T1>::Tau &_itf) -> decltype(auto) {
                     auto t_ = _itf.next;
                     return [&]() {
                       auto t = rec(t_);
                       return ITree<decltype(t->run())>::tau(t);
                     }();
                   },
                   [&](const typename ITree<T1>::Vis &_itf) -> decltype(auto) {
                     auto e = _itf.effect;
                     auto k = _itf.cont;
                     return itree_vis(
                         e, [=](std::any x) mutable { return rec(k(x)); });
                   }},
        ot);
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
