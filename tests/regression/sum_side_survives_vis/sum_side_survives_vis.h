#ifndef INCLUDED_SUM_SIDE_SURVIVES_VIS
#define INCLUDED_SUM_SIDE_SURVIVES_VIS

#include "obj.h"
#include <any>
#include <crane_itree.h>
#include <variant>

enum class AE;
enum class AE { A0 };

struct SumSideSurvivesVis {
  static std::shared_ptr<ITree<uint64_t>> tl();
  static std::shared_ptr<ITree<uint64_t>> tr();
  static std::shared_ptr<ITree<uint64_t>> vr();

  template <typename T1 = void>
  static uint64_t side(const Sum1<AE, AE, crane::obj> &e) {
    if (std::holds_alternative<typename Sum1<AE, AE, crane::obj>::Inl1>(
            e.v())) {
      return UINT64_C(1);
    } else {
      return UINT64_C(2);
    }
  }

  static uint64_t first_side(const std::shared_ptr<ITree<uint64_t>> &t);
  static inline const uint64_t left_side = first_side(tl());
  static inline const uint64_t right_side = first_side(tr());
  static inline const uint64_t right_vis = first_side(vr());
};

#endif // INCLUDED_SUM_SIDE_SURVIVES_VIS
