#ifndef INCLUDED_OPPOSITE_PROPERTY_TRANSFER_TRACE
#define INCLUDED_OPPOSITE_PROPERTY_TRANSFER_TRACE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct OppositePropertyTransferTraceCase {
  struct PreStableCategory {
    unsigned int ps_tag;
    unsigned int ps_shift;
    std::function<unsigned int(unsigned int)> ps_Susp;
    std::function<unsigned int(unsigned int)> ps_Loop;
    std::function<unsigned int(unsigned int)> ps_eta;
    std::function<unsigned int(unsigned int)> ps_epsilon;

    // ACCESSORS
    __attribute__((pure)) PreStableCategory clone() const {
      return PreStableCategory{(*(this)).ps_tag,  (*(this)).ps_shift,
                               (*(this)).ps_Susp, (*(this)).ps_Loop,
                               (*(this)).ps_eta,  (*(this)).ps_epsilon};
    }
  };

  __attribute__((pure)) static PreStableCategory
  opposite_prestable_category(const PreStableCategory &pS);

  struct LeftStableWitness {
    unsigned int lsw_seed;
    unsigned int lsw_value;

    // ACCESSORS
    __attribute__((pure)) LeftStableWitness clone() const {
      return LeftStableWitness{(*(this)).lsw_seed, (*(this)).lsw_value};
    }
  };

  struct RightStableWitness {
    unsigned int rsw_seed;
    unsigned int rsw_value;

    // ACCESSORS
    __attribute__((pure)) RightStableWitness clone() const {
      return RightStableWitness{(*(this)).rsw_seed, (*(this)).rsw_value};
    }
  };

  struct Triangle1Witness {
    unsigned int t1_seed;
    unsigned int t1_value;

    // ACCESSORS
    __attribute__((pure)) Triangle1Witness clone() const {
      return Triangle1Witness{(*(this)).t1_seed, (*(this)).t1_value};
    }
  };

  struct Triangle2Witness {
    unsigned int t2_seed;
    unsigned int t2_value;

    // ACCESSORS
    __attribute__((pure)) Triangle2Witness clone() const {
      return Triangle2Witness{(*(this)).t2_seed, (*(this)).t2_value};
    }
  };

  using is_left_semi_stable = LeftStableWitness;
  using is_right_semi_stable = RightStableWitness;
  using satisfies_triangle_1 = Triangle1Witness;
  using satisfies_triangle_2 = Triangle2Witness;
  template <typename a, typename b>
  using EquivT = std::pair<std::function<b(a)>, std::function<a(b)>>;

  struct LeftProperty {
    unsigned int lp_seed;
    unsigned int lp_value;
    unsigned int lp_tag;

    // ACCESSORS
    __attribute__((pure)) LeftProperty clone() const {
      return LeftProperty{(*(this)).lp_seed, (*(this)).lp_value,
                          (*(this)).lp_tag};
    }
  };

  struct RightProperty {
    unsigned int rp_seed;
    unsigned int rp_value;
    unsigned int rp_tag;

    // ACCESSORS
    __attribute__((pure)) RightProperty clone() const {
      return RightProperty{(*(this)).rp_seed, (*(this)).rp_value,
                           (*(this)).rp_tag};
    }
  };

  __attribute__((pure)) static is_left_semi_stable
  right_stable_gives_opposite_left(const PreStableCategory &_x,
                                   const RightStableWitness &h);
  __attribute__((
      pure)) static EquivT<satisfies_triangle_1, satisfies_triangle_2>
  triangle_identity_duality(const PreStableCategory &_x);
  __attribute__((pure)) static LeftProperty
  sample_left_property(const PreStableCategory &pS,
                       const LeftStableWitness &h_left,
                       const Triangle1Witness &_x);
  __attribute__((pure)) static EquivT<LeftProperty, RightProperty>
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
      PreStableCategory{7u,
                        4u,
                        [](const unsigned int &x) { return (x + 10u); },
                        [](const unsigned int &x) { return (x + 3u); },
                        [](const unsigned int &x) { return (x + 20u); },
                        [](const unsigned int &x) { return (x + 5u); }};
  static inline const is_right_semi_stable sample_right_stable =
      RightStableWitness{6u, 11u};
  static inline const satisfies_triangle_2 sample_triangle2 =
      Triangle2Witness{8u, 16u};
  static inline const RightProperty sample_right_property =
      theorem_doubling_principle_final<LeftProperty, RightProperty>(
          dual_property_equiv, sample_left_property, sample_category,
          sample_right_stable, sample_triangle2);
  static inline const unsigned int sample_opposite_tag =
      opposite_prestable_category(sample_category).ps_tag;
  static inline const unsigned int sample_opposite_loop_value =
      opposite_prestable_category(sample_category).ps_Loop(5u);
  static inline const unsigned int sample_result_seed =
      sample_right_property.rp_seed;
  static inline const unsigned int sample_result_value =
      sample_right_property.rp_value;
  static inline const unsigned int sample_result_tag =
      sample_right_property.rp_tag;
  static inline const unsigned int sample_checksum =
      ((((sample_opposite_tag + sample_opposite_loop_value) +
         sample_result_seed) +
        sample_result_value) +
       sample_result_tag);
};

#endif // INCLUDED_OPPOSITE_PROPERTY_TRANSFER_TRACE
