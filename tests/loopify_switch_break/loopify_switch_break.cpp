#include "loopify_switch_break.h"

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
      const auto &[t, v] = a0;
      switch (t) {
      case Tag::ADD: {
        _loop_acc = (_loop_acc + v);
        _loop_ops = crane_raw(a1);
        break;
      }
      case Tag::MUL: {
        _loop_acc = (_loop_acc * v);
        _loop_ops = crane_raw(a1);
        break;
      }
      case Tag::KEEP: {
        _loop_ops = crane_raw(a1);
        break;
      }
      default:
        std::unreachable();
      }
    }
  }
}

List<uint64_t> LoopifySwitchBreak::collect_ops(
    const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> &ops,
    uint64_t acc) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_acc = std::move(acc);
  const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> *_loop_ops = &ops;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Nil>(
            _loop_ops->v())) {
      *_write = std::make_shared<List<uint64_t>>(
          List<uint64_t>::cons(_loop_acc, List<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Cons>(
          _loop_ops->v());
      const auto &[t, v] = a0;
      switch (t) {
      case Tag::ADD: {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(_loop_acc, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_acc = (_loop_acc + v);
        _loop_ops = crane_raw(a1);
        continue;
        break;
      }
      case Tag::MUL: {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(_loop_acc, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_acc = (_loop_acc * v);
        _loop_ops = crane_raw(a1);
        continue;
        break;
      }
      case Tag::KEEP: {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(_loop_acc, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_ops = crane_raw(a1);
        continue;
        break;
      }
      default:
        std::unreachable();
      }
    }
  }
  return std::move(*_head);
}

uint64_t LoopifySwitchBreak::count_tag(
    LoopifySwitchBreak::Tag t,
    const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>
        &ops) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> *ops;
  };

  /// _Resume_t_: resumes after recursive call with _result.
  struct _Resume_t_ {};

  /// _Resume_t__1: resumes after recursive call with _result.
  struct _Resume_t__1 {};

  /// _Resume_t__2: resumes after recursive call with _result.
  struct _Resume_t__2 {};

  using _Frame = std::variant<_Enter, _Resume_t_, _Resume_t__1, _Resume_t__2>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&ops});
  /// Loopified count_tag: _Enter -> _Resume_t_ -> _Resume_t__1 -> _Resume_t__2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> &ops = *_f.ops;
      if (std::holds_alternative<
              typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Nil>(
              ops.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Cons>(
            ops.v());
        const auto &[t_, _x] = a0;
        switch (t) {
        case Tag::ADD: {
          switch (t_) {
          case Tag::ADD: {
            _stack.emplace_back(_Resume_t_{});
            _stack.emplace_back(_Enter{crane_raw(a1)});
            break;
          }
          default: {
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
          }
          break;
        }
        case Tag::MUL: {
          switch (t_) {
          case Tag::MUL: {
            _stack.emplace_back(_Resume_t__1{});
            _stack.emplace_back(_Enter{crane_raw(a1)});
            break;
          }
          default: {
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
          }
          break;
        }
        case Tag::KEEP: {
          switch (t_) {
          case Tag::KEEP: {
            _stack.emplace_back(_Resume_t__2{});
            _stack.emplace_back(_Enter{crane_raw(a1)});
            break;
          }
          default: {
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
          }
          break;
        }
        default:
          std::unreachable();
        }
      }
    } else if (std::holds_alternative<_Resume_t_>(_frame)) {
      auto _f = std::move(std::get<_Resume_t_>(_frame));
      _result = (std::move(_result) + 1);
    } else if (std::holds_alternative<_Resume_t__1>(_frame)) {
      auto _f = std::move(std::get<_Resume_t__1>(_frame));
      _result = (std::move(_result) + 1);
    } else {
      auto _f = std::move(std::get<_Resume_t__2>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}
