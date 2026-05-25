#include "loopify_switch_break.h"

/// eval_ops ops acc folds a list of (tag, value) pairs into an accumulator.
/// Each tag selects a different operation:
/// Add  -> acc + value
/// Mul  -> acc * value
/// Keep -> acc  (ignore value)
/// The function is structurally recursive on the list, and pattern-matches
/// on the tag inside the Cons branch.  Crane extracts the tag match as a
/// switch statement; loopification must emit break after each case.
uint64_t LoopifySwitchBreak::eval_ops(
    const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> &ops,
    uint64_t acc) {
  uint64_t _loop_acc = std::move(acc);
  const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> *_loop_ops = &ops;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Nil>(
            _loop_ops->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] = std::get<
          typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Cons>(
          _loop_ops->v());
      const LoopifySwitchBreak::Tag &t = a0.first;
      const uint64_t &v = a0.second;
      switch (t) {
      case Tag::ADD: {
        _loop_acc = (_loop_acc + v);
        _loop_ops = a1.get();
        break;
      }
      case Tag::MUL: {
        _loop_acc = (_loop_acc * v);
        _loop_ops = a1.get();
        break;
      }
      case Tag::KEEP: {
        _loop_ops = a1.get();
        break;
      }
      default:
        std::unreachable();
      }
    }
  }
}

/// A variant that builds a result list, so the recursive calls are
/// non-tail — this forces loopification to use continuation frames
/// (not just tail-call optimisation), exercising the break path in
/// non-tail switch branches.
List<uint64_t> LoopifySwitchBreak::collect_ops(
    const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> &ops,
    uint64_t
        acc) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t acc;
    const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> *ops;
  };

  /// _Resume_t: saves [acc], resumes after recursive call with _result.
  struct _Resume_t {
    uint64_t acc;
  };

  /// _Resume_t_1: saves [acc], resumes after recursive call with _result.
  struct _Resume_t_1 {
    uint64_t acc;
  };

  /// _Resume_t_2: saves [acc], resumes after recursive call with _result.
  struct _Resume_t_2 {
    uint64_t acc;
  };

  using _Frame = std::variant<_Enter, _Resume_t, _Resume_t_1, _Resume_t_2>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{acc, &ops});
  /// Loopified collect_ops: _Enter -> _Resume_t -> _Resume_t_1 -> _Resume_t_2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t acc = _f.acc;
      const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> &ops = *_f.ops;
      if (std::holds_alternative<
              typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Nil>(
              ops.v())) {
        _result = List<uint64_t>::cons(acc, List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<
            typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Cons>(
            ops.v());
        const LoopifySwitchBreak::Tag &t = a0.first;
        const uint64_t &v = a0.second;
        switch (t) {
        case Tag::ADD: {
          _stack.emplace_back(_Resume_t{acc});
          _stack.emplace_back(_Enter{(acc + v), a1.get()});
          break;
        }
        case Tag::MUL: {
          _stack.emplace_back(_Resume_t_1{acc});
          _stack.emplace_back(_Enter{(acc * v), a1.get()});
          break;
        }
        case Tag::KEEP: {
          _stack.emplace_back(_Resume_t_2{acc});
          _stack.emplace_back(_Enter{acc, a1.get()});
          break;
        }
        default:
          std::unreachable();
        }
      }
    } else if (std::holds_alternative<_Resume_t>(_frame)) {
      auto _f = std::move(std::get<_Resume_t>(_frame));
      _result = List<uint64_t>::cons(_f.acc, _result);
    } else if (std::holds_alternative<_Resume_t_1>(_frame)) {
      auto _f = std::move(std::get<_Resume_t_1>(_frame));
      _result = List<uint64_t>::cons(_f.acc, _result);
    } else {
      auto _f = std::move(std::get<_Resume_t_2>(_frame));
      _result = List<uint64_t>::cons(_f.acc, _result);
    }
  }
  return _result;
}

/// count_tags tag ops counts how many times a given tag appears.
/// All three branches of the switch recurse; without break, EQ would
/// fall through to the next case and produce an incorrect count.
uint64_t LoopifySwitchBreak::count_tag(
    LoopifySwitchBreak::Tag t,
    const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> &ops) {
  if (std::holds_alternative<
          typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Nil>(
          ops.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<
        typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Cons>(
        ops.v());
    const LoopifySwitchBreak::Tag &t_ = a0.first;
    const uint64_t &_x = a0.second;
    switch (t) {
    case Tag::ADD: {
      switch (t_) {
      case Tag::ADD: {
        return (count_tag(t, *a1) + 1);
      }
      default: {
        return count_tag(t, *a1);
      }
      }
      break;
    }
    case Tag::MUL: {
      switch (t_) {
      case Tag::MUL: {
        return (count_tag(t, *a1) + 1);
      }
      default: {
        return count_tag(t, *a1);
      }
      }
      break;
    }
    case Tag::KEEP: {
      switch (t_) {
      case Tag::KEEP: {
        return (count_tag(t, *a1) + 1);
      }
      default: {
        return count_tag(t, *a1);
      }
      }
      break;
    }
    default:
      std::unreachable();
    }
  }
}
