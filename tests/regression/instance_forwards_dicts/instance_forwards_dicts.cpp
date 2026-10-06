#include "instance_forwards_dicts.h"

uint64_t
InstanceForwardsDicts::sum_exp(const InstanceForwardsDicts::exp<uint64_t> &e) {
  if (std::holds_alternative<
          typename InstanceForwardsDicts::exp<uint64_t>::Lit>(e.v())) {
    const auto &[a0, a1] =
        std::get<typename InstanceForwardsDicts::exp<uint64_t>::Lit>(e.v());
    switch (a0) {
    case Tag::A: {
      return a1;
    }
    case Tag::B: {
      return (UINT64_C(100) + a1);
    }
    default:
      std::unreachable();
    }
  } else if (std::holds_alternative<
                 typename InstanceForwardsDicts::exp<uint64_t>::Ops>(e.v())) {
    return UINT64_C(0);
  } else if (std::holds_alternative<
                 typename InstanceForwardsDicts::exp<uint64_t>::Neg>(e.v())) {
    const auto &[a0, a1] =
        std::get<typename InstanceForwardsDicts::exp<uint64_t>::Neg>(e.v());
    return (a0 + sum_exp(*a1));
  } else {
    const auto &[a0] =
        std::get<typename InstanceForwardsDicts::exp<uint64_t>::EMeta>(e.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<
            typename InstanceForwardsDicts::meta<uint64_t>::MNull>(_sv0.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a00] =
          std::get<typename InstanceForwardsDicts::meta<uint64_t>::MExp>(
              _sv0.v());
      return sum_exp(*a00);
    }
  }
}
