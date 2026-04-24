#include <opposite_property_transfer_trace.h>

#include <functional>
#include <type_traits>
#include <utility>

__attribute__((pure)) OppositePropertyTransferTraceCase::PreStableCategory
OppositePropertyTransferTraceCase::opposite_prestable_category(
    const OppositePropertyTransferTraceCase::PreStableCategory &pS) {
  return PreStableCategory{pS.ps_tag,  pS.ps_shift,   pS.ps_Loop,
                           pS.ps_Susp, pS.ps_epsilon, pS.ps_eta};
}

__attribute__((pure)) OppositePropertyTransferTraceCase::is_left_semi_stable
OppositePropertyTransferTraceCase::right_stable_gives_opposite_left(
    const OppositePropertyTransferTraceCase::PreStableCategory &,
    const OppositePropertyTransferTraceCase::RightStableWitness &h) {
  unsigned int rsw_seed0 = h.rsw_seed;
  unsigned int rsw_value0 = h.rsw_value;
  return LeftStableWitness{rsw_seed0, rsw_value0};
}

__attribute__((pure)) OppositePropertyTransferTraceCase::EquivT<
    OppositePropertyTransferTraceCase::satisfies_triangle_1,
    OppositePropertyTransferTraceCase::satisfies_triangle_2>
OppositePropertyTransferTraceCase::triangle_identity_duality(
    const OppositePropertyTransferTraceCase::PreStableCategory &) {
  return std::make_pair(
      [](const OppositePropertyTransferTraceCase::Triangle1Witness &h) {
        unsigned int t1_seed0 = h.t1_seed;
        unsigned int t1_value0 = h.t1_value;
        return Triangle2Witness{t1_seed0, t1_value0};
      },
      [](const OppositePropertyTransferTraceCase::Triangle2Witness &h) {
        unsigned int t2_seed0 = h.t2_seed;
        unsigned int t2_value0 = h.t2_value;
        return Triangle1Witness{t2_seed0, t2_value0};
      });
}

__attribute__((pure)) OppositePropertyTransferTraceCase::LeftProperty
OppositePropertyTransferTraceCase::sample_left_property(
    const OppositePropertyTransferTraceCase::PreStableCategory &pS,
    const OppositePropertyTransferTraceCase::LeftStableWitness &h_left,
    const OppositePropertyTransferTraceCase::Triangle1Witness &) {
  unsigned int lsw_seed0 = h_left.lsw_seed;
  unsigned int lsw_value0 = h_left.lsw_value;
  return LeftProperty{lsw_seed0, ((lsw_value0 + pS.ps_shift) + pS.ps_tag),
                      pS.ps_tag};
}

__attribute__((pure)) OppositePropertyTransferTraceCase::EquivT<
    OppositePropertyTransferTraceCase::LeftProperty,
    OppositePropertyTransferTraceCase::RightProperty>
OppositePropertyTransferTraceCase::dual_property_equiv(
    const OppositePropertyTransferTraceCase::PreStableCategory &) {
  return std::make_pair(
      [](const OppositePropertyTransferTraceCase::LeftProperty &h) {
        unsigned int lp_seed0 = h.lp_seed;
        unsigned int lp_value0 = h.lp_value;
        unsigned int lp_tag0 = h.lp_tag;
        return RightProperty{lp_seed0, lp_value0, lp_tag0};
      },
      [](const OppositePropertyTransferTraceCase::RightProperty &h) {
        unsigned int rp_seed0 = h.rp_seed;
        unsigned int rp_value0 = h.rp_value;
        unsigned int rp_tag0 = h.rp_tag;
        return LeftProperty{rp_seed0, rp_value0, rp_tag0};
      });
}
