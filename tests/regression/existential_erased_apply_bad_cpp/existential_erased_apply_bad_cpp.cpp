#include "existential_erased_apply_bad_cpp.h"

uint64_t ExistentialErasedApplyBadCpp::force(
    const ExistentialErasedApplyBadCpp::dyn &d) {
  const auto &[a, a1] = d;
  return a1(a);
}

List<ExistentialErasedApplyBadCpp::dyn>
ExistentialErasedApplyBadCpp::mk(uint64_t n) {
  return List<ExistentialErasedApplyBadCpp::dyn>::cons(
      dyn::dyn0(n, std::function<uint64_t(std::any)>(
                       [](const std::any &k) -> uint64_t {
                         return std::any_cast<uint64_t>(k);
                       })),
      List<ExistentialErasedApplyBadCpp::dyn>::cons(
          dyn::dyn0(
              std::make_pair(n, (n + 1)),
              std::function<uint64_t(std::any)>([](const std::any &p)
                                                    -> uint64_t {
                return (
                    crane_any_cast<std::pair<uint64_t, uint64_t>>(p).first +
                    crane_any_cast<std::pair<uint64_t, uint64_t>>(p).second);
              })),
          List<ExistentialErasedApplyBadCpp::dyn>::cons(
              dyn::dyn0(List<uint64_t>::cons(
                            n, List<uint64_t>::cons(
                                   n, List<uint64_t>::cons(
                                          n, List<uint64_t>::nil()))),
                        std::function<uint64_t(std::any)>(
                            [](const std::any &l) -> uint64_t {
                              return std::any_cast<List<uint64_t>>(l).length();
                            })),
              List<ExistentialErasedApplyBadCpp::dyn>::nil())));
}

uint64_t ExistentialErasedApplyBadCpp::total(
    const List<ExistentialErasedApplyBadCpp::dyn> &l) {
  if (std::holds_alternative<
          typename List<ExistentialErasedApplyBadCpp::dyn>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename List<ExistentialErasedApplyBadCpp::dyn>::Cons>(l.v());
    return (force(a0) + total(*a1));
  }
}

uint64_t ExistentialErasedApplyBadCpp::run(uint64_t n) { return total(mk(n)); }
