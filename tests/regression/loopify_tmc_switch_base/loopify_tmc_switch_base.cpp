#include "loopify_tmc_switch_base.h"

/// A base case of a tail-modulo-cons loop inside an enum's match.
///
/// Tail modulo cons builds the result in a while (true) loop and leaves it
/// from a base case by break, once the base value is in place.  A match on
/// an enum is a switch, where break leaves only the switch: the loop went
/// round again on the same input and never returned.  f Blue reaches a base
/// case at once, inside the switch; f Red and f Green reach one through
/// the recursion, the second nested in a match inside the switch.
LoopifyTmcSwitchBase::num
LoopifyTmcSwitchBase::f(LoopifyTmcSwitchBase::Color c,
                        const LoopifyTmcSwitchBase::num &n) {
  std::optional<LoopifyTmcSwitchBase::num> _root{};
  std::shared_ptr<LoopifyTmcSwitchBase::num> *_write = nullptr;
  const LoopifyTmcSwitchBase::num *_loop_n = &n;
  LoopifyTmcSwitchBase::Color _loop_c = c;
  while (true) {
    if (std::holds_alternative<typename LoopifyTmcSwitchBase::num::Z>(
            _loop_n->v())) {
      auto _value = num::z();
      (_write ? *(*_write = std::make_shared<LoopifyTmcSwitchBase::num>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[n0] =
          std::get<typename LoopifyTmcSwitchBase::num::Su>(_loop_n->v());
      switch (_loop_c) {
      case Color::RED: {
        _loop_n = crane_raw(n0);
        _loop_c = Color::GREEN;
        continue;
        break;
      }
      case Color::GREEN: {
        auto _cell = typename LoopifyTmcSwitchBase::num::Su(nullptr);
        LoopifyTmcSwitchBase::num &_node =
            (_write ? *(*_write = std::make_shared<LoopifyTmcSwitchBase::num>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyTmcSwitchBase::num::Su>(_node.v_mut()).n;
        _loop_n = crane_raw(n0);
        _loop_c = Color::BLUE;
        continue;
        break;
      }
      case Color::BLUE: {
        auto &&_sv = *n0;
        if (std::holds_alternative<typename LoopifyTmcSwitchBase::num::Z>(
                _sv.v())) {
          auto _value = num::su(num::su(num::z()));
          (_write ? *(*_write = std::make_shared<LoopifyTmcSwitchBase::num>(
                          std::move(_value)))
                  : _root.emplace(std::move(_value)));
          return std::move(*_root);
        } else {
          _loop_n = crane_raw(n0);
          _loop_c = Color::RED;
          continue;
        }
        break;
      }
      default:
        std::unreachable();
      }
    }
  }
  return std::move(*_root);
}

LoopifyTmcSwitchBase::num LoopifyTmcSwitchBase::of_nat(uint64_t n) {
  std::optional<LoopifyTmcSwitchBase::num> _root{};
  std::shared_ptr<LoopifyTmcSwitchBase::num> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = num::z();
      (_write ? *(*_write = std::make_shared<LoopifyTmcSwitchBase::num>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = typename LoopifyTmcSwitchBase::num::Su(nullptr);
      LoopifyTmcSwitchBase::num &_node =
          (_write ? *(*_write = std::make_shared<LoopifyTmcSwitchBase::num>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LoopifyTmcSwitchBase::num::Su>(_node.v_mut()).n;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t
LoopifyTmcSwitchBase::to_nat(const LoopifyTmcSwitchBase::num
                                 &n) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyTmcSwitchBase::num *n;
  };

  /// CraneCont_Su: resumes after recursive call, then processes rest.
  struct CraneCont_Su {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Su>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&n});
  /// Loopified to_nat: CraneEnter -> CraneCont_Su.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyTmcSwitchBase::num &n = *_f.n;
      if (std::holds_alternative<typename LoopifyTmcSwitchBase::num::Z>(
              n.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[n0] =
            std::get<typename LoopifyTmcSwitchBase::num::Su>(n.v());
        _stack.emplace_back(CraneCont_Su{});
        _stack.emplace_back(CraneEnter{crane_raw(n0)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Su>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t LoopifyTmcSwitchBase::run_f(LoopifyTmcSwitchBase::Color c,
                                     uint64_t n) {
  return to_nat(f(c, of_nat(n)));
}
