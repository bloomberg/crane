#include "opposite_property_transfer_trace.h"

OppositePropertyTransferTraceCase::PreStableCategory
OppositePropertyTransferTraceCase::opposite_prestable_category(
    const OppositePropertyTransferTraceCase::PreStableCategory &pS) {
  return PreStableCategory{pS.ps_tag,  pS.ps_shift,   pS.ps_Loop,
                           pS.ps_Susp, pS.ps_epsilon, pS.ps_eta};
}

OppositePropertyTransferTraceCase::is_left_semi_stable
OppositePropertyTransferTraceCase::right_stable_gives_opposite_left(
    const OppositePropertyTransferTraceCase::PreStableCategory &,
    const OppositePropertyTransferTraceCase::RightStableWitness &h) {
  uint64_t rsw_seed0 = h.rsw_seed;
  uint64_t rsw_value0 = h.rsw_value;
  return LeftStableWitness{rsw_seed0, rsw_value0};
}

OppositePropertyTransferTraceCase::EquivT<
    OppositePropertyTransferTraceCase::satisfies_triangle_1,
    OppositePropertyTransferTraceCase::satisfies_triangle_2>
OppositePropertyTransferTraceCase::triangle_identity_duality(
    const OppositePropertyTransferTraceCase::PreStableCategory &) {
  return std::make_pair(
      [](const OppositePropertyTransferTraceCase::Triangle1Witness &h) {
        uint64_t t1_seed0 = h.t1_seed;
        uint64_t t1_value0 = h.t1_value;
        return Triangle2Witness{t1_seed0, t1_value0};
      },
      [](const OppositePropertyTransferTraceCase::Triangle2Witness &h) {
        uint64_t t2_seed0 = h.t2_seed;
        uint64_t t2_value0 = h.t2_value;
        return Triangle1Witness{t2_seed0, t2_value0};
      });
}

OppositePropertyTransferTraceCase::LeftProperty
OppositePropertyTransferTraceCase::sample_left_property(
    const OppositePropertyTransferTraceCase::PreStableCategory &pS,
    const OppositePropertyTransferTraceCase::LeftStableWitness &h_left,
    const OppositePropertyTransferTraceCase::Triangle1Witness &) {
  uint64_t lsw_seed0 = h_left.lsw_seed;
  uint64_t lsw_value0 = h_left.lsw_value;
  return LeftProperty{lsw_seed0, ((lsw_value0 + pS.ps_shift) + pS.ps_tag),
                      pS.ps_tag};
}

OppositePropertyTransferTraceCase::EquivT<
    OppositePropertyTransferTraceCase::LeftProperty,
    OppositePropertyTransferTraceCase::RightProperty>
OppositePropertyTransferTraceCase::dual_property_equiv(
    const OppositePropertyTransferTraceCase::PreStableCategory &) {
  return std::make_pair(
      [](const OppositePropertyTransferTraceCase::LeftProperty &h) {
        uint64_t lp_seed0 = h.lp_seed;
        uint64_t lp_value0 = h.lp_value;
        uint64_t lp_tag0 = h.lp_tag;
        return RightProperty{lp_seed0, lp_value0, lp_tag0};
      },
      [](const OppositePropertyTransferTraceCase::RightProperty &h) {
        uint64_t rp_seed0 = h.rp_seed;
        uint64_t rp_value0 = h.rp_value;
        uint64_t rp_tag0 = h.rp_tag;
        return LeftProperty{rp_seed0, rp_value0, rp_tag0};
      });
}
