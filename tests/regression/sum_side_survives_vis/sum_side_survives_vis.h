#pragma once

#include "obj.h"
#include <crane_itree.h>
#include <cstdint>
#include <utility>
#include <variant>

enum class AE;
enum class AE { A0 };

struct SumSideSurvivesVis {
  static std::shared_ptr<ITree<uint64_t>> tl();
  static std::shared_ptr<ITree<uint64_t>> tr();
  static std::shared_ptr<ITree<uint64_t>> vr();
  static uint64_t side(const Sum1<AE, AE, crane::obj> &e);
  static uint64_t first_side(const std::shared_ptr<ITree<uint64_t>> &t);
  static inline const uint64_t left_side = first_side(tl());
  static inline const uint64_t right_side = first_side(tr());
  static inline const uint64_t right_vis = first_side(vr());
};
