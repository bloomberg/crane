#include "existential_erased_apply_bad_cpp.h"

uint64_t ExistentialErasedApplyBadCpp::force(
    const ExistentialErasedApplyBadCpp::dyn &d) {
  const auto &[a, a1] = d;
  return a1(a);
}

List<ExistentialErasedApplyBadCpp::dyn>
ExistentialErasedApplyBadCpp::mk(uint64_t n) {
  return List<ExistentialErasedApplyBadCpp::dyn>::cons(
      dyn::dyn0(n, crane::fn<uint64_t(crane::obj)>(
                       [](const crane::obj &k) -> uint64_t {
                         return crane::any_cast<uint64_t>(k);
                       })),
      List<ExistentialErasedApplyBadCpp::dyn>::cons(
          dyn::dyn0(
              std::make_pair(crane::obj(n), crane::obj((n + 1))),
              crane::fn<uint64_t(crane::obj)>([](const crane::obj &p)
                                                  -> uint64_t {
                return (
                    crane::any_cast<uint64_t>(
                        crane::any_cast<std::pair<crane::obj, crane::obj>>(p)
                            .first) +
                    crane::any_cast<uint64_t>(
                        crane::any_cast<std::pair<crane::obj, crane::obj>>(p)
                            .second));
              })),
          List<ExistentialErasedApplyBadCpp::dyn>::cons(
              dyn::dyn0(List<crane::obj>::cons(
                            n, List<crane::obj>::cons(
                                   n, List<crane::obj>::cons(
                                          n, List<crane::obj>::nil()))),
                        crane::fn<uint64_t(crane::obj)>(
                            [](const crane::obj &l) -> uint64_t {
                              return List<uint64_t>(
                                         crane::any_cast<List<crane::obj>>(l))
                                  .length();
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
