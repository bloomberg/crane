#include "PairDerefValue.h"

#include "Datatypes.h"

namespace PairDerefValue {

bool NatKey::key_eq_dec(
    const Datatypes::Nat &n,
    const Datatypes::Nat
        &x0) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const Datatypes::Nat *x0;
    const Datatypes::Nat *n;
  };

  /// _Cont_S: resumes after recursive call, then processes rest.
  struct _Cont_S {};

  using _Frame = std::variant<_Enter, _Cont_S>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&x0, &n});
  /// Loopified key_eq_dec: _Enter -> _Cont_S.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
          _stack.emplace_back(_Cont_S{});
          _stack.emplace_back(_Enter{a00.get(), a0.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_S>(_frame));
      bool _rc1 = std::move(_result);
      if (_rc1) {
        _result = true;
      } else {
        _result = false;
      }
    }
  }
  return _result;
}

} // namespace PairDerefValue
