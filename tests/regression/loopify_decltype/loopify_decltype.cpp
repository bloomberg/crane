#include "loopify_decltype.h"

/// Minimal trigger: fold over a list with a conditional per-element
/// contribution.
uint64_t LoopifyDecltype::count_true(const List<bool> &xs) {
  {
    const List<bool> &_lc1_l = xs;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const List<bool> *_lc1_loop_l = &_lc1_l;
    while (true) {
      if (std::holds_alternative<typename List<bool>::Nil>(_lc1_loop_l->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<bool>::Cons>(_lc1_loop_l->v());
        _lc1_loop_acc = (_lc1_loop_acc + (a0 ? UINT64_C(1) : UINT64_C(0)));
        _lc1_loop_l = crane_raw(a1);
      }
    }
  }
}

uint64_t LoopifyDecltype::sum_flagged(const List<LoopifyDecltype::item> &xs) {
  {
    const List<LoopifyDecltype::item> &_lc1_l = xs;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const List<LoopifyDecltype::item> *_lc1_loop_l = &_lc1_l;
    while (true) {
      if (std::holds_alternative<typename List<LoopifyDecltype::item>::Nil>(
              _lc1_loop_l->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyDecltype::item>::Cons>(
                _lc1_loop_l->v());
        _lc1_loop_acc =
            (_lc1_loop_acc + (a0.item_flag ? a0.item_val : UINT64_C(0)));
        _lc1_loop_l = crane_raw(a1);
      }
    }
  }
}
