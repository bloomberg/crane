#include "reuse_moved_capture_renamed.h"

ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>>
ReuseMovedCaptureRenamed::adders(
    ReuseMovedCaptureRenamed::mylist<ReuseMovedCaptureRenamed::tree> ts) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>>> _root{};
  crane::rc<ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>>> *_write =
      nullptr;
  const ReuseMovedCaptureRenamed::mylist<ReuseMovedCaptureRenamed::tree> *_loop_ts =
      &ts;
  while (true) {
    if (std::holds_alternative<typename ReuseMovedCaptureRenamed::mylist<
            ReuseMovedCaptureRenamed::tree>::Mynil>(_loop_ts->v())) {
      auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      (_write ? *(*_write = crane::make_rc<ReuseMovedCaptureRenamed::mylist<
                      crane::fn<uint64_t(uint64_t)>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<typename ReuseMovedCaptureRenamed::mylist<
          ReuseMovedCaptureRenamed::tree>::Mycons>(_loop_ts->v());
      const ReuseMovedCaptureRenamed::mylist<ReuseMovedCaptureRenamed::tree> &a1_value =
          *a1;
      auto _cell = typename ReuseMovedCaptureRenamed::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons(
          [=, a0 = std::move(a0)](uint64_t _x0) -> uint64_t {
            return a0.peek(_x0);
          },
          nullptr);
      ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>> &_node =
          (_write ? *(*_write = crane::make_rc<ReuseMovedCaptureRenamed::mylist<
                          crane::fn<uint64_t(uint64_t)>>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename ReuseMovedCaptureRenamed::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mycons>(_node.v_mut()).a1;
      _loop_ts = &a1_value;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t ReuseMovedCaptureRenamed::apply_all(
    const ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>> &fs,
    uint64_t x) {
  // Explicit stack replaces the non-tail recursion of apply_all: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>> *fs;
  };

  struct _after_apply_all_in_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using _frame = std::variant<_call, _after_apply_all_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&fs});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>> &fs =
          *_f.fs;
      if (std::holds_alternative<typename ReuseMovedCaptureRenamed::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(fs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename ReuseMovedCaptureRenamed::mylist<
                crane::fn<uint64_t(uint64_t)>>::Mycons>(fs.v());
        _stack.emplace_back(_after_apply_all_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_apply_all_in_Mycons>(_popped));
      _stack.pop_back();
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      _result = a0(x) + _result;
    }
  }
  return _result;
}
