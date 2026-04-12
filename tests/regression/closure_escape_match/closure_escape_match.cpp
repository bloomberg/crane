#include <closure_escape_match.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// Return a closure wrapped in option — prevents uncurrying.
/// The closure captures a pattern variable hd (a shared_ptr),
/// which is an inlined _args.d_a0 inside the std::visit callback.
__attribute__((pure)) std::optional<
    std::function<std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>(
        std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>)>>
ClosureEscapeMatch::make_prepender_opt(
    const std::shared_ptr<ClosureEscapeMatch::mylist<
        std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename ClosureEscapeMatch::mylist<std::shared_ptr<
                 ClosureEscapeMatch::mylist<unsigned int>>>::Mynil &)
              -> std::optional<std::function<std::shared_ptr<
                  ClosureEscapeMatch::mylist<unsigned int>>(
                  std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>)>> {
            return std::optional<std::function<std::shared_ptr<
                ClosureEscapeMatch::mylist<unsigned int>>(
                std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>)>>();
          },
          [](const typename ClosureEscapeMatch::mylist<std::shared_ptr<
                 ClosureEscapeMatch::mylist<unsigned int>>>::Mycons &_args)
              -> std::optional<std::function<std::shared_ptr<
                  ClosureEscapeMatch::mylist<unsigned int>>(
                  std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>)>> {
            return std::make_optional<std::function<std::shared_ptr<
                ClosureEscapeMatch::mylist<unsigned int>>(
                std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>)>>(
                [=](const std::shared_ptr<
                    ClosureEscapeMatch::mylist<unsigned int>> &x) mutable {
                  return app<unsigned int>(_args.d_a0, x);
                });
          }},
      l->v());
}

/// Return a closure in a pair — prevents uncurrying.
/// Captures pattern variables x and xs.
__attribute__((pure)) std::optional<
    std::function<std::pair<unsigned int, unsigned int>(std::monostate)>>
ClosureEscapeMatch::make_pair_fn_opt(
    const std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename ClosureEscapeMatch::mylist<unsigned int>::Mynil &)
              -> std::optional<std::function<
                  std::pair<unsigned int, unsigned int>(std::monostate)>> {
            return std::optional<std::function<
                std::pair<unsigned int, unsigned int>(std::monostate)>>();
          },
          [](const typename ClosureEscapeMatch::mylist<unsigned int>::Mycons
                 &_args)
              -> std::optional<std::function<
                  std::pair<unsigned int, unsigned int>(std::monostate)>> {
            return std::make_optional<std::function<
                std::pair<unsigned int, unsigned int>(std::monostate)>>(
                [=](const std::monostate) mutable {
                  return std::make_pair(_args.d_a0,
                                        length<unsigned int>(_args.d_a1));
                });
          }},
      l->v());
}

/// Nested matches with closures returned in option.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
ClosureEscapeMatch::nested_closure_opt(
    const std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>> &a,
    const std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>> &b) {
  return std::visit(
      Overloaded{
          [&](const typename ClosureEscapeMatch::mylist<unsigned int>::Mynil &)
              -> std::optional<std::function<unsigned int(unsigned int)>> {
            return std::visit(
                Overloaded{[](const typename ClosureEscapeMatch::mylist<
                               unsigned int>::Mynil &)
                               -> std::optional<
                                   std::function<unsigned int(unsigned int)>> {
                             return std::optional<
                                 std::function<unsigned int(unsigned int)>>();
                           },
                           [](const typename ClosureEscapeMatch::mylist<
                               unsigned int>::Mycons &_args0)
                               -> std::optional<
                                   std::function<unsigned int(unsigned int)>> {
                             return std::make_optional<
                                 std::function<unsigned int(unsigned int)>>(
                                 [=](const unsigned int n) mutable {
                                   return (_args0.d_a0 + n);
                                 });
                           }},
                b->v());
          },
          [&](const typename ClosureEscapeMatch::mylist<unsigned int>::Mycons
                  &_args)
              -> std::optional<std::function<unsigned int(unsigned int)>> {
            return std::visit(
                Overloaded{[&](const typename ClosureEscapeMatch::mylist<
                               unsigned int>::Mynil &)
                               -> std::optional<
                                   std::function<unsigned int(unsigned int)>> {
                             return std::make_optional<
                                 std::function<unsigned int(unsigned int)>>(
                                 [=](const unsigned int n) mutable {
                                   return (_args.d_a0 + n);
                                 });
                           },
                           [&](const typename ClosureEscapeMatch::mylist<
                               unsigned int>::Mycons &_args0)
                               -> std::optional<
                                   std::function<unsigned int(unsigned int)>> {
                             return std::make_optional<
                                 std::function<unsigned int(unsigned int)>>(
                                 [=](const unsigned int n) mutable {
                                   return ((_args.d_a0 + _args0.d_a0) + n);
                                 });
                           }},
                b->v());
          }},
      a->v());
}

/// Closure stored in a product, capturing shared_ptr pattern variable.
__attribute__((pure)) std::pair<
    unsigned int,
    std::function<std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>(
        std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>)>>
ClosureEscapeMatch::closure_in_pair(
    const std::shared_ptr<ClosureEscapeMatch::mylist<
        std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename ClosureEscapeMatch::mylist<
              std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>>::Mynil
                 &) -> std::pair<unsigned int,
                                 std::function<std::shared_ptr<
                                     ClosureEscapeMatch::mylist<unsigned int>>(
                                     std::shared_ptr<ClosureEscapeMatch::mylist<
                                         unsigned int>>)>> {
            return std::make_pair(
                0u, [](std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>
                           x) { return x; });
          },
          [](const typename ClosureEscapeMatch::mylist<std::shared_ptr<
                 ClosureEscapeMatch::mylist<unsigned int>>>::Mycons &_args)
              -> std::pair<
                  unsigned int,
                  std::function<
                      std::shared_ptr<ClosureEscapeMatch::mylist<unsigned int>>(
                          std::shared_ptr<
                              ClosureEscapeMatch::mylist<unsigned int>>)>> {
            return std::make_pair(
                length<unsigned int>(_args.d_a0),
                [=](const std::shared_ptr<
                    ClosureEscapeMatch::mylist<unsigned int>> &x) mutable {
                  return app<unsigned int>(_args.d_a0, x);
                });
          }},
      l->v());
}
