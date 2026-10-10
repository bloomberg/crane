#include "itree_ret_family_from_result.h"

uint64_t ItreeRetFamilyFromResult::result(
    uint64_t fuel, const Itree<Sum1<ItreeRetFamilyFromResult::AE,
                                    ItreeRetFamilyFromResult::BE, crane::obj>,
                               Sum<uint64_t, uint64_t>> &t) {
  if (fuel <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t f = fuel - 1;
    auto &&_sv = t.observe();
    if (std::holds_alternative<typename ItreeF<
            Sum1<ItreeRetFamilyFromResult::AE, ItreeRetFamilyFromResult::BE,
                 crane::obj>,
            Sum<uint64_t, uint64_t>,
            Itree<Sum1<ItreeRetFamilyFromResult::AE,
                       ItreeRetFamilyFromResult::BE, crane::obj>,
                  Sum<uint64_t, uint64_t>>>::RetF>(_sv.v())) {
      const auto &[r0] = std::get<
          typename ItreeF<Sum1<ItreeRetFamilyFromResult::AE,
                               ItreeRetFamilyFromResult::BE, crane::obj>,
                          Sum<uint64_t, uint64_t>,
                          Itree<Sum1<ItreeRetFamilyFromResult::AE,
                                     ItreeRetFamilyFromResult::BE, crane::obj>,
                                Sum<uint64_t, uint64_t>>>::RetF>(_sv.v());
      if (std::holds_alternative<typename Sum<uint64_t, uint64_t>::Inl>(
              r0.v())) {
        const auto &[a00] =
            std::get<typename Sum<uint64_t, uint64_t>::Inl>(r0.v());
        return (UINT64_C(100) + a00);
      } else {
        const auto &[a00] =
            std::get<typename Sum<uint64_t, uint64_t>::Inr>(r0.v());
        return a00;
      }
    } else if (std::holds_alternative<typename ItreeF<
                   Sum1<ItreeRetFamilyFromResult::AE,
                        ItreeRetFamilyFromResult::BE, crane::obj>,
                   Sum<uint64_t, uint64_t>,
                   Itree<Sum1<ItreeRetFamilyFromResult::AE,
                              ItreeRetFamilyFromResult::BE, crane::obj>,
                         Sum<uint64_t, uint64_t>>>::TauF>(_sv.v())) {
      const auto &[t0] = std::get<
          typename ItreeF<Sum1<ItreeRetFamilyFromResult::AE,
                               ItreeRetFamilyFromResult::BE, crane::obj>,
                          Sum<uint64_t, uint64_t>,
                          Itree<Sum1<ItreeRetFamilyFromResult::AE,
                                     ItreeRetFamilyFromResult::BE, crane::obj>,
                                Sum<uint64_t, uint64_t>>>::TauF>(_sv.v());
      return result(f, t0);
    } else {
      return UINT64_C(0);
    }
  }
}
