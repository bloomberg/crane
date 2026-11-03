#include "reuse_moved_capture_renamed.h"

ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>>
ReuseMovedCaptureRenamed::adders(
    ReuseMovedCaptureRenamed::mylist<ReuseMovedCaptureRenamed::tree> ts) {
  crane::rc<ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>>>
      _head{};
  crane::rc<ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>>>
      *_write = &_head;
  const ReuseMovedCaptureRenamed::mylist<ReuseMovedCaptureRenamed::tree>
      *_loop_ts = &ts;
  while (true) {
    if (std::holds_alternative<typename ReuseMovedCaptureRenamed::mylist<
            ReuseMovedCaptureRenamed::tree>::Mynil>(_loop_ts->v())) {
      *_write = crane::make_rc<
          ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>>>(
          mylist<crane::fn<uint64_t(uint64_t)>>::mynil());
      break;
    } else {
      const auto &[a0, a1] = std::get<typename ReuseMovedCaptureRenamed::mylist<
          ReuseMovedCaptureRenamed::tree>::Mycons>(_loop_ts->v());
      const ReuseMovedCaptureRenamed::mylist<ReuseMovedCaptureRenamed::tree>
          &a1_value = *a1;
      auto _cell = crane::make_rc<
          ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>>>(
          typename ReuseMovedCaptureRenamed::
              mylist<crane::fn<uint64_t(uint64_t)>>::Mycons(
                  [=, a0 = std::move(a0)](uint64_t _x0) -> uint64_t {
                    return a0.peek(_x0);
                  },
                  nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename ReuseMovedCaptureRenamed::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>((*_write)->v_mut())
                    .a1;
      _loop_ts = &a1_value;
      continue;
    }
  }
  return std::move(*_head);
}

uint64_t ReuseMovedCaptureRenamed::apply_all(
    const ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>> &fs,
    uint64_t x) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    const ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>> *fs;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&fs});
  /// Loopified apply_all: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const ReuseMovedCaptureRenamed::mylist<crane::fn<uint64_t(uint64_t)>>
          &fs = *_f.fs;
      if (std::holds_alternative<typename ReuseMovedCaptureRenamed::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(fs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename ReuseMovedCaptureRenamed::mylist<
                crane::fn<uint64_t(uint64_t)>>::Mycons>(fs.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      _result = (a0(x) + std::move(_result));
    }
  }
  return _result;
}
