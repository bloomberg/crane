#include "translate_alias_source.h"

uint64_t TranslateAliasSource::run(
    uint64_t fuel, const Itree<Sum1<TranslateAliasSource::CE,
                                    Sum1<TranslateAliasSource::AE,
                                         TranslateAliasSource::BE, crane::obj>,
                                    crane::obj>,
                               uint64_t> &t) {
  if (fuel <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t f = fuel - 1;
    auto &&_sv = t.observe();
    if (std::holds_alternative<typename ItreeF<
            Sum1<TranslateAliasSource::CE,
                 Sum1<TranslateAliasSource::AE, TranslateAliasSource::BE,
                      crane::obj>,
                 crane::obj>,
            uint64_t,
            Itree<Sum1<TranslateAliasSource::CE,
                       Sum1<TranslateAliasSource::AE, TranslateAliasSource::BE,
                            crane::obj>,
                       crane::obj>,
                  uint64_t>>::RetF>(_sv.v())) {
      const auto &[r0] = std::get<
          typename ItreeF<Sum1<TranslateAliasSource::CE,
                               Sum1<TranslateAliasSource::AE,
                                    TranslateAliasSource::BE, crane::obj>,
                               crane::obj>,
                          uint64_t,
                          Itree<Sum1<TranslateAliasSource::CE,
                                     Sum1<TranslateAliasSource::AE,
                                          TranslateAliasSource::BE, crane::obj>,
                                     crane::obj>,
                                uint64_t>>::RetF>(_sv.v());
      return r0;
    } else if (std::holds_alternative<typename ItreeF<
                   Sum1<TranslateAliasSource::CE,
                        Sum1<TranslateAliasSource::AE, TranslateAliasSource::BE,
                             crane::obj>,
                        crane::obj>,
                   uint64_t,
                   Itree<Sum1<TranslateAliasSource::CE,
                              Sum1<TranslateAliasSource::AE,
                                   TranslateAliasSource::BE, crane::obj>,
                              crane::obj>,
                         uint64_t>>::TauF>(_sv.v())) {
      const auto &[t0] = std::get<
          typename ItreeF<Sum1<TranslateAliasSource::CE,
                               Sum1<TranslateAliasSource::AE,
                                    TranslateAliasSource::BE, crane::obj>,
                               crane::obj>,
                          uint64_t,
                          Itree<Sum1<TranslateAliasSource::CE,
                                     Sum1<TranslateAliasSource::AE,
                                          TranslateAliasSource::BE, crane::obj>,
                                     crane::obj>,
                                uint64_t>>::TauF>(_sv.v());
      return run(f, t0);
    } else {
      const auto &[x, e0] = std::get<
          typename ItreeF<Sum1<TranslateAliasSource::CE,
                               Sum1<TranslateAliasSource::AE,
                                    TranslateAliasSource::BE, crane::obj>,
                               crane::obj>,
                          uint64_t,
                          Itree<Sum1<TranslateAliasSource::CE,
                                     Sum1<TranslateAliasSource::AE,
                                          TranslateAliasSource::BE, crane::obj>,
                                     crane::obj>,
                                uint64_t>>::VisF>(_sv.v());
      if (std::holds_alternative<
              typename Sum1<TranslateAliasSource::CE,
                            Sum1<TranslateAliasSource::AE,
                                 TranslateAliasSource::BE, crane::obj>,
                            crane::obj>::Inl1>(x.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a00] =
            std::get<typename Sum1<TranslateAliasSource::CE,
                                   Sum1<TranslateAliasSource::AE,
                                        TranslateAliasSource::BE, crane::obj>,
                                   crane::obj>::Inr1>(x.v());
        if (std::holds_alternative<
                typename Sum1<TranslateAliasSource::AE,
                              TranslateAliasSource::BE, crane::obj>::Inl1>(
                a00.v())) {
          return run(f, e0(UINT64_C(41)));
        } else {
          return UINT64_C(0);
        }
      }
    }
  }
}
