#include "loopify_local_fix_inner_callback.h"

/// A local fixpoint whose recursive calls are all made by a fixpoint
/// inside it.
///
/// f calls itself only from ack_m, a fixpoint it applies in place.  A
/// machine for f leaves those calls where they are, in ack_m's
/// closure, but drops the self-parameter they recurse through, so the
/// loop it emitted named an undeclared _self_f.  A local machine does not
/// adopt an inner fixpoint as a second entry, so f is left recursing
/// natively.
uint64_t
LoopifyLocalFixInnerCallback::ack(const std::pair<uint64_t, uint64_t> &p) {
  auto f_impl = [&](auto &_self_f, uint64_t m, uint64_t n) -> uint64_t {
    auto ack_m = [&](uint64_t n0) -> uint64_t {
      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        uint64_t n0;
      };
      /// CraneCont_pn: saves [pm], resumes after recursive call, then processes
      /// rest.
      struct CraneCont_pn {
        uint64_t pm;
      };
      using CraneFrame = std::variant<CraneEnter, CraneCont_pn>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{n0});
      /// Loopified ack_m: CraneEnter -> CraneCont_pn.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          uint64_t n0 = _f.n0;
          if (m <= 0) {
            _result = (n0 + 1);
          } else {
            uint64_t pm = m - 1;
            if (n0 <= 0) {
              _result = _self_f(_self_f, pm, UINT64_C(1));
            } else {
              uint64_t pn = n0 - 1;
              _stack.emplace_back(CraneCont_pn{pm});
              _stack.emplace_back(CraneEnter{pn});
            }
          }
        } else {
          auto _f = std::move(std::get<CraneCont_pn>(_frame));
          uint64_t pm = _f.pm;
          _result = _self_f(_self_f, pm, std::move(_result));
        }
      }
      return _result;
    };
    return ack_m(n);
  };
  {
    uint64_t _lc1_m = p.first;
    uint64_t _lc1_n = p.second;
    return f_impl(f_impl, _lc1_m, _lc1_n);
  }
}
