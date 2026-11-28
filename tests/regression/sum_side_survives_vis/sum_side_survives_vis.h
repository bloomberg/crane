#pragma once

#include "obj.h"
#include <crane_itree.h>
#include <cstdint>
#include <utility>

enum class AE;
enum class AE { A0 };

struct SumSideSurvivesVis {
  static std::shared_ptr<ITree<uint64_t>> tl();
  static std::shared_ptr<ITree<uint64_t>> tr();
  static std::shared_ptr<ITree<uint64_t>> vr();

  template <typename T1> static uint64_t side(const Sum1<AE, AE, T1> &e) {
    if (std::holds_alternative<typename std::decay_t<decltype(e)>::Inl1>(e.v())) {
      const auto &_x =
          std::get<typename std::decay_t<decltype(e)>::Inl1>(e.v()).a0;
      return UINT64_C(1);
    } else {
      const auto &_x =
          std::get<typename std::decay_t<decltype(e)>::Inr1>(e.v()).a0;
      return UINT64_C(2);
    }
  }

  static uint64_t first_side(const std::shared_ptr<ITree<uint64_t>> &t);
  static inline const uint64_t left_side = first_side(tl());
  static inline const uint64_t right_side = first_side(tr());
  static inline const uint64_t right_vis = first_side(vr());
};
