#include "PairDerefValue.h"

#include "Datatypes.h"

namespace PairDerefValue {
bool NatKey::key_eq_dec(const Datatypes::Nat &n, const Datatypes::Nat &x0) {
  // Explicit stack replaces the non-tail recursion of key_eq_dec: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const Datatypes::Nat *x0;
    const Datatypes::Nat *n;
  };

  struct _after_key_eq_dec_in_S {};

  using _frame = std::variant<_call, _after_key_eq_dec_in_S>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x0, &n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
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
          _stack.emplace_back(_after_key_eq_dec_in_S{});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_key_eq_dec_in_S>(_popped));
      _stack.pop_back();
      if (std::move(_result)) {
        _result = true;
      } else {
        _result = false;
      }
    }
  }
  return _result;
}
} // namespace PairDerefValue
