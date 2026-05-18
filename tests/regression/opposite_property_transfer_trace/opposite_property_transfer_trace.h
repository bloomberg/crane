#ifndef INCLUDED_OPPOSITE_PROPERTY_TRANSFER_TRACE
#define INCLUDED_OPPOSITE_PROPERTY_TRANSFER_TRACE

#include <functional>
#include <utility>

struct OppositePropertyTransferTraceCase {
  struct PreStableCategory {
    uint64_t ps_tag;
    uint64_t ps_shift;
    std::function<uint64_t(uint64_t)> ps_Susp;
    std::function<uint64_t(uint64_t)> ps_Loop;
    std::function<uint64_t(uint64_t)> ps_eta;
    std::function<uint64_t(uint64_t)> ps_epsilon;

    // ACCESSORS
    PreStableCategory clone() const {
      return PreStableCategory{(*this).ps_tag,  (*this).ps_shift,
                               (*this).ps_Susp, (*this).ps_Loop,
                               (*this).ps_eta,  (*this).ps_epsilon};
    }
  };

  static PreStableCategory
  opposite_prestable_category(const PreStableCategory &pS);

  struct LeftStableWitness {
    uint64_t lsw_seed;
    uint64_t lsw_value;

    // ACCESSORS
    LeftStableWitness clone() const {
      return LeftStableWitness{(*this).lsw_seed, (*this).lsw_value};
    }
  };

  struct RightStableWitness {
    uint64_t rsw_seed;
    uint64_t rsw_value;

    // ACCESSORS
    RightStableWitness clone() const {
      return RightStableWitness{(*this).rsw_seed, (*this).rsw_value};
    }
  };

  struct Triangle1Witness {
    uint64_t t1_seed;
    uint64_t t1_value;

    // ACCESSORS
    Triangle1Witness clone() const {
      return Triangle1Witness{(*this).t1_seed, (*this).t1_value};
    }
  };

  struct Triangle2Witness {
    uint64_t t2_seed;
    uint64_t t2_value;

    // ACCESSORS
    Triangle2Witness clone() const {
      return Triangle2Witness{(*this).t2_seed, (*this).t2_value};
    }
  };

  using is_left_semi_stable = LeftStableWitness;
  using is_right_semi_stable = RightStableWitness;
  using satisfies_triangle_1 = Triangle1Witness;
  using satisfies_triangle_2 = Triangle2Witness;
  template <typename a, typename b>
  using EquivT = std::pair<std::function<b(a)>, std::function<a(b)>>;

  struct LeftProperty {
    uint64_t lp_seed;
    uint64_t lp_value;
    uint64_t lp_tag;

    // ACCESSORS
    LeftProperty clone() const {
      return LeftProperty{(*this).lp_seed, (*this).lp_value, (*this).lp_tag};
    }
  };

  struct RightProperty {
    uint64_t rp_seed;
    uint64_t rp_value;
    uint64_t rp_tag;

    // ACCESSORS
    RightProperty clone() const {
      return RightProperty{(*this).rp_seed, (*this).rp_value, (*this).rp_tag};
    }
  };

  static is_left_semi_stable
  right_stable_gives_opposite_left(const PreStableCategory &_x,
                                   const RightStableWitness &h);
  static EquivT<satisfies_triangle_1, satisfies_triangle_2>
  triangle_identity_duality(const PreStableCategory &_x);
  static LeftProperty sample_left_property(const PreStableCategory &pS,
                                           const LeftStableWitness &h_left,
                                           const Triangle1Witness &_x);
  static EquivT<LeftProperty, RightProperty>
  dual_property_equiv(const PreStableCategory &_x);

  template <typename T1 = void, typename T2, typename F0, typename F1>
  static T2 theorem_doubling_principle_correct(
      F0 &&h_dual, F1 &&h_theorem, const PreStableCategory &pS,
      const LeftStableWitness &h_left_op, const Triangle1Witness &h_tri1_op) {
    std::pair<std::function<T2(T1)>, std::function<T1(T2)>> e =
        h_dual(opposite_prestable_category(pS));
    const std::function<T2(T1)> &q = e.first;
    const std::function<T1(T2)> &_x = e.second;
    return q(h_theorem(opposite_prestable_category(pS), h_left_op, h_tri1_op));
  }

  template <typename T1 = void, typename T2, typename F0, typename F1>
  static T2 theorem_doubling_principle_final(F0 &&h_dual, F1 &&h_theorem,
                                             const PreStableCategory &pS,
                                             const RightStableWitness &h_right,
                                             const Triangle2Witness &h_tri2) {
    return theorem_doubling_principle_correct<T1, T2>(
        h_dual, h_theorem, pS, right_stable_gives_opposite_left(pS, h_right),
        [=]() mutable {
          std::pair<std::function<Triangle2Witness(Triangle1Witness)>,
                    std::function<Triangle1Witness(Triangle2Witness)>>
              e = triangle_identity_duality(opposite_prestable_category(pS));
          const std::function<Triangle2Witness(Triangle1Witness)> &_x = e.first;
          const std::function<Triangle1Witness(Triangle2Witness)> &s = e.second;
          return s(h_tri2);
        }());
  }

  static inline const PreStableCategory sample_category =
      PreStableCategory{UINT64_C(7),
                        UINT64_C(4),
                        [](uint64_t x) { return (x + UINT64_C(10)); },
                        [](uint64_t x) { return (x + UINT64_C(3)); },
                        [](uint64_t x) { return (x + UINT64_C(20)); },
                        [](uint64_t x) { return (x + UINT64_C(5)); }};
  static inline const is_right_semi_stable sample_right_stable =
      RightStableWitness{UINT64_C(6), UINT64_C(11)};
  static inline const satisfies_triangle_2 sample_triangle2 =
      Triangle2Witness{UINT64_C(8), UINT64_C(16)};
  static inline const RightProperty sample_right_property =
      theorem_doubling_principle_final<LeftProperty, RightProperty>(
          dual_property_equiv, sample_left_property, sample_category,
          sample_right_stable, sample_triangle2);
  static inline const uint64_t sample_opposite_tag =
      opposite_prestable_category(sample_category).ps_tag;
  static inline const uint64_t sample_opposite_loop_value =
      opposite_prestable_category(sample_category).ps_Loop(UINT64_C(5));
  static inline const uint64_t sample_result_seed =
      sample_right_property.rp_seed;
  static inline const uint64_t sample_result_value =
      sample_right_property.rp_value;
  static inline const uint64_t sample_result_tag = sample_right_property.rp_tag;
  static inline const uint64_t sample_checksum =
      ((((sample_opposite_tag + sample_opposite_loop_value) +
         sample_result_seed) +
        sample_result_value) +
       sample_result_tag);
};

#endif // INCLUDED_OPPOSITE_PROPERTY_TRANSFER_TRACE
