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
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
                                                      const itreeF_t<T2> ot) {
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
