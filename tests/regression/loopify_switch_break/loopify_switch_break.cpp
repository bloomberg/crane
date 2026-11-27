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
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> *_loop_ops = &ops;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Nil>(
            _loop_ops->v())) {
      return acc;
    } else {
      const auto &[a0, a1] = std::get<
          typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Cons>(
          _loop_ops->v());
      const auto &[t, v] = a0;
      switch (t) {
      case Tag::ADD: {
        acc = acc + v;
        _loop_ops = crane_raw(a1);
        break;
      }
      case Tag::MUL: {
        acc = acc * v;
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

/// A variant that builds a result list, so the recursive calls are
/// non-tail — this forces loopification to use continuation frames
/// (not just tail-call optimisation), exercising the break path in
/// non-tail switch branches.
List<uint64_t> LoopifySwitchBreak::collect_ops(
    const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> &ops,
    uint64_t acc) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> *_loop_ops = &ops;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Nil>(
            _loop_ops->v())) {
      auto _value = List<uint64_t>::cons(acc, List<uint64_t>::nil());
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Cons>(
          _loop_ops->v());
      const auto &[t, v] = a0;
      switch (t) {
      case Tag::ADD: {
        auto _cell = typename List<uint64_t>::Cons(acc, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        acc = acc + v;
        _loop_ops = crane_raw(a1);
        continue;
        break;
      }
      case Tag::MUL: {
        auto _cell = typename List<uint64_t>::Cons(acc, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        acc = acc * v;
        _loop_ops = crane_raw(a1);
        continue;
        break;
      }
      case Tag::KEEP: {
        auto _cell = typename List<uint64_t>::Cons(acc, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_ops = crane_raw(a1);
        continue;
        break;
      }
      default:
        std::unreachable();
      }
    }
  }
  return std::move(*_root);
}

/// count_tags tag ops counts how many times a given tag appears.
/// All three branches of the switch recurse; without break, EQ would
/// fall through to the next case and produce an incorrect count.
uint64_t LoopifySwitchBreak::count_tag(
    LoopifySwitchBreak::Tag t,
    const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> &ops) {
  // Explicit stack replaces the non-tail recursion of count_tag: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> *ops;
  };

  struct _after_count_tag_in_pair {};

  struct _after_count_tag_in_pair_2 {};

  struct _after_count_tag_in_pair_3 {};

  using _frame =
      std::variant<_call, _after_count_tag_in_pair, _after_count_tag_in_pair_2,
                   _after_count_tag_in_pair_3>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&ops});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<std::pair<LoopifySwitchBreak::Tag, uint64_t>> &ops = *_f.ops;
      if (std::holds_alternative<
              typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Nil>(
              ops.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename List<std::pair<LoopifySwitchBreak::Tag, uint64_t>>::Cons>(
            ops.v());
        const auto &[t_, _] = a0;
        switch (t) {
        case Tag::ADD: {
          switch (t_) {
          case Tag::ADD: {
            _stack.emplace_back(_after_count_tag_in_pair{});
            _stack.emplace_back(_call{crane_raw(a1)});
            break;
          }
          default: {
            _stack.emplace_back(_call{crane_raw(a1)});
          }
          }
          break;
        }
        case Tag::MUL: {
          switch (t_) {
          case Tag::MUL: {
            _stack.emplace_back(_after_count_tag_in_pair_2{});
            _stack.emplace_back(_call{crane_raw(a1)});
            break;
          }
          default: {
            _stack.emplace_back(_call{crane_raw(a1)});
          }
          }
          break;
        }
        case Tag::KEEP: {
          switch (t_) {
          case Tag::KEEP: {
            _stack.emplace_back(_after_count_tag_in_pair_3{});
            _stack.emplace_back(_call{crane_raw(a1)});
            break;
          }
          default: {
            _stack.emplace_back(_call{crane_raw(a1)});
          }
          }
          break;
        }
        default:
          std::unreachable();
        }
      }
    } else if (std::holds_alternative<_after_count_tag_in_pair>(_popped)) {
      auto _f = std::move(std::get<_after_count_tag_in_pair>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    } else if (std::holds_alternative<_after_count_tag_in_pair_2>(_popped)) {
      auto _f = std::move(std::get<_after_count_tag_in_pair_2>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    } else {
      auto _f = std::move(std::get<_after_count_tag_in_pair_3>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}
