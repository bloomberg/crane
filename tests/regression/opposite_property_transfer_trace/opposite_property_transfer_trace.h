#ifndef INCLUDED_OPPOSITE_PROPERTY_TRANSFER_TRACE
#define INCLUDED_OPPOSITE_PROPERTY_TRANSFER_TRACE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct OppositePropertyTransferTraceCase {
  struct PreStableCategory {
    unsigned int ps_tag;
    unsigned int ps_shift;
    std::function<unsigned int(unsigned int)> ps_Susp;
    std::function<unsigned int(unsigned int)> ps_Loop;
    std::function<unsigned int(unsigned int)> ps_eta;
    std::function<unsigned int(unsigned int)> ps_epsilon;
  };

  static std::shared_ptr<PreStableCategory>
  opposite_prestable_category(std::shared_ptr<PreStableCategory> pS);

  struct LeftStableWitness {
    unsigned int lsw_seed;
    unsigned int lsw_value;
  };

  struct RightStableWitness {
    unsigned int rsw_seed;
    unsigned int rsw_value;
  };

  struct Triangle1Witness {
    unsigned int t1_seed;
    unsigned int t1_value;
  };

  struct Triangle2Witness {
    unsigned int t2_seed;
    unsigned int t2_value;
  };

  using is_left_semi_stable = std::shared_ptr<LeftStableWitness>;
  using is_right_semi_stable = std::shared_ptr<RightStableWitness>;
  using satisfies_triangle_1 = std::shared_ptr<Triangle1Witness>;
  using satisfies_triangle_2 = std::shared_ptr<Triangle2Witness>;
  template <typename a, typename b>
  using EquivT = std::pair<std::function<b(a)>, std::function<a(b)>>;

  struct LeftProperty {
    unsigned int lp_seed;
    unsigned int lp_value;
    unsigned int lp_tag;
  };

  struct RightProperty {
    unsigned int rp_seed;
    unsigned int rp_value;
    unsigned int rp_tag;
  };

  __attribute__((pure)) static is_left_semi_stable
  right_stable_gives_opposite_left(
      const std::shared_ptr<PreStableCategory> &_x,
      const std::shared_ptr<RightStableWitness> &h);
  __attribute__((
      pure)) static EquivT<satisfies_triangle_1, satisfies_triangle_2>
  triangle_identity_duality(const std::shared_ptr<PreStableCategory> &_x);
  static std::shared_ptr<LeftProperty>
  sample_left_property(std::shared_ptr<PreStableCategory> pS,
                       const std::shared_ptr<LeftStableWitness> &h_left,
                       const std::shared_ptr<Triangle1Witness> &_x);
  __attribute__((pure)) static EquivT<std::shared_ptr<LeftProperty>,
                                      std::shared_ptr<RightProperty>>
  dual_property_equiv(const std::shared_ptr<PreStableCategory> &_x);

  template <typename T1 = void, typename T2, typename F0, typename F1>
  static T2 theorem_doubling_principle_correct(
      F0 &&h_dual, F1 &&h_theorem, const std::shared_ptr<PreStableCategory> &pS,
      const std::shared_ptr<LeftStableWitness> &h_left_op,
      const std::shared_ptr<Triangle1Witness> &h_tri1_op) {
    std::pair<std::function<T2(T1)>, std::function<T1(T2)>> e =
        h_dual(opposite_prestable_category(pS));
    std::function<T2(T1)> q = e.first;
    std::function<T1(T2)> _x = e.second;
    return q(h_theorem(opposite_prestable_category(pS), h_left_op, h_tri1_op));
  }

  template <typename T1 = void, typename T2, typename F0, typename F1>
  static T2 theorem_doubling_principle_final(
      F0 &&h_dual, F1 &&h_theorem, const std::shared_ptr<PreStableCategory> &pS,
      const std::shared_ptr<RightStableWitness> &h_right,
      const std::shared_ptr<Triangle2Witness> &h_tri2) {
    return theorem_doubling_principle_correct<T1, T2>(
        h_dual, h_theorem, pS, right_stable_gives_opposite_left(pS, h_right),
        [&]() {
          std::pair<std::function<std::shared_ptr<Triangle2Witness>(
                        std::shared_ptr<Triangle1Witness>)>,
                    std::function<std::shared_ptr<Triangle1Witness>(
                        std::shared_ptr<Triangle2Witness>)>>
              e = triangle_identity_duality(opposite_prestable_category(pS));
          std::function<std::shared_ptr<Triangle2Witness>(
              std::shared_ptr<Triangle1Witness>)>
              _x = e.first;
          std::function<std::shared_ptr<Triangle1Witness>(
              std::shared_ptr<Triangle2Witness>)>
              s = e.second;
          return s(h_tri2);
        }());
  }

  static inline const std::shared_ptr<PreStableCategory> sample_category =
      std::make_shared<PreStableCategory>(
          PreStableCategory{7u, 4u, [](unsigned int x) { return (x + 10u); },
                            [](unsigned int x) { return (x + 3u); },
                            [](unsigned int x) { return (x + 20u); },
                            [](unsigned int x) { return (x + 5u); }});
  static inline const is_right_semi_stable sample_right_stable =
      std::make_shared<RightStableWitness>(RightStableWitness{6u, 11u});
  static inline const satisfies_triangle_2 sample_triangle2 =
      std::make_shared<Triangle2Witness>(Triangle2Witness{8u, 16u});
  static inline const std::shared_ptr<RightProperty> sample_right_property =
      theorem_doubling_principle_final<std::shared_ptr<LeftProperty>,
                                       std::shared_ptr<RightProperty>>(
          dual_property_equiv, sample_left_property, sample_category,
          sample_right_stable, sample_triangle2);
  static inline const unsigned int sample_opposite_tag =
      opposite_prestable_category(sample_category)->ps_tag;
  static inline const unsigned int sample_opposite_loop_value =
      opposite_prestable_category(sample_category)->ps_Loop(5u);
  static inline const unsigned int sample_result_seed =
      sample_right_property->rp_seed;
  static inline const unsigned int sample_result_value =
      sample_right_property->rp_value;
  static inline const unsigned int sample_result_tag =
      sample_right_property->rp_tag;
  static inline const unsigned int sample_checksum =
      ((((sample_opposite_tag + sample_opposite_loop_value) +
         sample_result_seed) +
        sample_result_value) +
       sample_result_tag);
};

#endif // INCLUDED_OPPOSITE_PROPERTY_TRANSFER_TRACE
