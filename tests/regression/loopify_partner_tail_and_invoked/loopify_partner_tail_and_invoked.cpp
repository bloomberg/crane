#include "loopify_partner_tail_and_invoked.h"

/// walk calls its partner step both as a tail call and as the operand
/// of an addition, and step calls walk back where its body runs.  Its
/// machine continues in step's body at the tail call and enters a copy of
/// step at the other, whose calls of walk are turns of the one machine:
/// no call between the two runs on the C++ stack, however deep.
uint64_t LoopifyPartnerTailAndInvoked::walk(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneEnter_step_entry: captures varying parameters for each recursive
  /// call.
  struct CraneEnter_step_entry {
    uint64_t n0;
  };

  /// CraneCont2: resumes after recursive call, then processes rest.
  struct CraneCont2 {};

  /// CraneCont_m: resumes after recursive call, then processes rest.
  struct CraneCont_m {};

  /// CraneCont_m0: resumes after recursive call, then processes rest.
  struct CraneCont_m0 {};

  using CraneFrame = std::variant<CraneEnter, CraneEnter_step_entry, CraneCont2,
                                  CraneCont_m, CraneCont_m0>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified walk: CraneEnter -> CraneCont2 -> CraneCont_m -> CraneCont_m0.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        if ((UINT64_C(2) ? m % UINT64_C(2) : m) == UINT64_C(0)) {
          if (m <= 0) {
            _result = UINT64_C(1);
          } else {
            uint64_t m0 = m - 1;
            _stack.emplace_back(CraneCont_m0{});
            _stack.emplace_back(CraneEnter{m0});
          }
        } else {
          _stack.emplace_back(CraneCont2{});
          _stack.emplace_back(CraneEnter_step_entry{m});
        }
      }
    } else if (std::holds_alternative<CraneEnter_step_entry>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_step_entry>(_frame));
      uint64_t n0 = _f.n0;
      if (n0 <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t m = n0 - 1;
        _stack.emplace_back(CraneCont_m{});
        _stack.emplace_back(CraneEnter{m});
      }
    } else if (std::holds_alternative<CraneCont2>(_frame)) {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      _result = (UINT64_C(1) + std::move(_result));
    } else if (std::holds_alternative<CraneCont_m>(_frame)) {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      _result = (std::move(_result) + 1);
    } else {
      auto _f = std::move(std::get<CraneCont_m0>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t LoopifyPartnerTailAndInvoked::step(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneEnter_walk_entry: captures varying parameters for each recursive
  /// call.
  struct CraneEnter_walk_entry {
    uint64_t n0;
  };

  /// CraneCont2: resumes after recursive call, then processes rest.
  struct CraneCont2 {};

  /// CraneCont_m: resumes after recursive call, then processes rest.
  struct CraneCont_m {};

  using CraneFrame =
      std::variant<CraneEnter, CraneEnter_walk_entry, CraneCont2, CraneCont_m>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified step: CraneEnter -> CraneCont2 -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{});
        _stack.emplace_back(CraneEnter_walk_entry{m});
      }
    } else if (std::holds_alternative<CraneEnter_walk_entry>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_walk_entry>(_frame));
      uint64_t n0 = _f.n0;
      if (n0 <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n0 - 1;
        if ((UINT64_C(2) ? m % UINT64_C(2) : m) == UINT64_C(0)) {
          _stack.emplace_back(CraneEnter{m});
        } else {
          _stack.emplace_back(CraneCont2{});
          _stack.emplace_back(CraneEnter{m});
        }
      }
    } else if (std::holds_alternative<CraneCont2>(_frame)) {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      _result = (UINT64_C(1) + std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}
