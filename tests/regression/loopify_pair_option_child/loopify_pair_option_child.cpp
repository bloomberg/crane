#include "loopify_pair_option_child.h"

uint64_t
LoopifyPairOptionChild::sum(const LoopifyPairOptionChild::tree
                                &t) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    LoopifyPairOptionChild::tree t;
  };

  /// CraneCont_u: saves [x, _tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_u {
    uint64_t x;
    uint64_t _tmp2;
  };

  /// CraneCont_x: saves [x, o], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_x {
    uint64_t x;
    std::optional<LoopifyPairOptionChild::tree> o;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_u, CraneCont_x>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{t});
  /// Loopified sum: CraneEnter -> CraneCont_u -> CraneCont_x.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyPairOptionChild::tree &t = std::move(_f.t);
      if (std::holds_alternative<typename LoopifyPairOptionChild::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPairOptionChild::tree::Node>(t.v());
        const auto &[x, o] = (*a1);
        _stack.emplace_back(CraneCont_x{x, o});
        _stack.emplace_back(CraneEnter{*a0});
      }
    } else if (std::holds_alternative<CraneCont_u>(_frame)) {
      auto _f = std::move(std::get<CraneCont_u>(_frame));
      uint64_t x = _f.x;
      _result = ((_f._tmp2 + x) + std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont_x>(_frame));
      uint64_t x = _f.x;
      std::optional<LoopifyPairOptionChild::tree> o = std::move(_f.o);
      uint64_t _tmp2 = std::move(_result);
      uint64_t _tmp1;
      if (o.has_value()) {
        const LoopifyPairOptionChild::tree &u = *o;
        _stack.emplace_back(CraneCont_u{x, _tmp2});
        _stack.emplace_back(CraneEnter{u});
      } else {
        _tmp1 = UINT64_C(0);
        {
          _result = ((_tmp2 + x) + _tmp1);
        }
      }
    }
  }
  return _result;
}
