#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <crane_itree.h>
#include <cstdint>
#include <utility>
#include <variant>

enum class AE;
enum class BE;
enum class AE { A0 };
enum class BE { B0, B1 };
BE relabel(AE _x);

struct TranslateAppliesHandler {
  static std::shared_ptr<ITree<uint64_t>> t0();
  static std::shared_ptr<ITree<uint64_t>> relabelled();
  static std::shared_ptr<ITree<uint64_t>> injected();
  static uint64_t which_b(BE e);
  static uint64_t which_side(const Sum1<AE, AE, crane::obj> &e);
  static uint64_t b_of(const std::shared_ptr<ITree<uint64_t>> &t);
  static uint64_t side_of(const std::shared_ptr<ITree<uint64_t>> &t);
  static inline const uint64_t relabelled_event = b_of(relabelled());
  static inline const uint64_t injected_side = side_of(injected());
};
