#ifndef INCLUDED_TRANSLATE_APPLIES_HANDLER
#define INCLUDED_TRANSLATE_APPLIES_HANDLER

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <crane_itree.h>
#include <utility>
#include <variant>

enum class AE;
enum class BE;
enum class AE { A0 };
enum class BE { B0, B1 };

template <typename T1 = void> BE relabel(AE) { return BE::B1; }

struct TranslateAppliesHandler {
  static std::shared_ptr<ITree<uint64_t>> t0();
  static std::shared_ptr<ITree<uint64_t>> relabelled();
  static std::shared_ptr<ITree<uint64_t>> injected();

  template <typename T1 = void> static uint64_t which_b(BE e) {
    switch (e) {
    case BE::B0: {
      return UINT64_C(0);
    }
    case BE::B1: {
      return UINT64_C(1);
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1 = void>
  static uint64_t which_side(const Sum1<AE, AE, crane::obj> &e) {
    if (std::holds_alternative<typename Sum1<AE, AE, crane::obj>::Inl1>(
            e.v())) {
      return UINT64_C(1);
    } else {
      return UINT64_C(2);
    }
  }

  static uint64_t b_of(const std::shared_ptr<ITree<uint64_t>> &t);
  static uint64_t side_of(const std::shared_ptr<ITree<uint64_t>> &t);
  static inline const uint64_t relabelled_event = b_of(relabelled());
  static inline const uint64_t injected_side = side_of(injected());
};

#endif // INCLUDED_TRANSLATE_APPLIES_HANDLER
