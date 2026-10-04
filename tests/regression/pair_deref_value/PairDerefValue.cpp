#include "PairDerefValue.h"

#include "Datatypes.h"

namespace PairDerefValue {

bool NatKey::key_eq_dec(
    const Datatypes::Nat &n,
    const Datatypes::Nat &x0) { /// CraneEnter: captures varying parameters for
                                /// each recursive call.

  struct CraneEnter {
    const Datatypes::Nat *x0;
    const Datatypes::Nat *n;
  };

  /// CraneCont_S: resumes after recursive call, then processes rest.
  struct CraneCont_S {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_S>;
  bool _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&x0, &n});
  /// Loopified key_eq_dec: CraneEnter -> CraneCont_S.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const Datatypes::Nat &x0 = *_f.x0;
      const Datatypes::Nat &n = *_f.n;
      if (std::holds_alternative<typename Datatypes::Nat::O>(n.v())) {
        if (std::holds_alternative<typename Datatypes::Nat::O>(x0.v())) {
          _result = true;
        } else {
          _result = false;
        }
      } else {
        const auto &[a0] = std::get<typename Datatypes::Nat::S>(n.v());
        if (std::holds_alternative<typename Datatypes::Nat::O>(x0.v())) {
          _result = false;
        } else {
          const auto &[a00] = std::get<typename Datatypes::Nat::S>(x0.v());
          _stack.emplace_back(CraneCont_S{});
          _stack.emplace_back(CraneEnter{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_S>(_frame));
      bool _tmp1 = std::move(_result);
      if (_tmp1) {
        _result = true;
      } else {
        _result = false;
      }
    }
  }
  return _result;
}

} // namespace PairDerefValue
