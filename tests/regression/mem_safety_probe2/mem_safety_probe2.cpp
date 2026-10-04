#include "mem_safety_probe2.h"

/// TEST 7: Closure escaping through a list, then applied.
MemSafetyProbe2::mylist<uint64_t> MemSafetyProbe2::map_apply(
    const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> &fs,
    uint64_t x) {
  std::shared_ptr<MemSafetyProbe2::mylist<uint64_t>> _head{};
  std::shared_ptr<MemSafetyProbe2::mylist<uint64_t>> *_write = &_head;
  const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> *_loop_fs = &fs;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe2::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mynil>(_loop_fs->v())) {
      *_write = std::make_shared<MemSafetyProbe2::mylist<uint64_t>>(
          mylist<uint64_t>::mynil());
      break;
    } else {
      const auto &[a0, a1] = std::get<typename MemSafetyProbe2::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>(_loop_fs->v());
      auto _cell = std::make_shared<MemSafetyProbe2::mylist<uint64_t>>(
          typename MemSafetyProbe2::mylist<uint64_t>::Mycons(a0(x), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename MemSafetyProbe2::mylist<uint64_t>::Mycons>(
                    (*_write)->v_mut())
                    .a1;
      _loop_fs = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_head);
}

uint64_t MemSafetyProbe2::mysum(const MemSafetyProbe2::mylist<uint64_t> &
                                    l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe2::mylist<uint64_t> *l;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified mysum: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe2::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe2::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe2::mylist<uint64_t>::Mycons>(l.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 13: Fold building tree from closures' results.
MemSafetyProbe2::tree MemSafetyProbe2::fold_tree_build(
    const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> &fs,
    uint64_t acc) {
  std::shared_ptr<MemSafetyProbe2::tree> _head{};
  std::shared_ptr<MemSafetyProbe2::tree> *_write = &_head;
  uint64_t _loop_acc = std::move(acc);
  const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> *_loop_fs = &fs;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe2::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mynil>(_loop_fs->v())) {
      *_write = std::make_shared<MemSafetyProbe2::tree>(tree::leaf());
      break;
    } else {
      const auto &[a0, a1] = std::get<typename MemSafetyProbe2::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>(_loop_fs->v());
      auto _cell = std::make_shared<MemSafetyProbe2::tree>(
          typename MemSafetyProbe2::tree::Node(
              nullptr, a0(_loop_acc),
              std::make_shared<MemSafetyProbe2::tree>(tree::leaf())));
      *_write = std::move(_cell);
      _write =
          &std::get<typename MemSafetyProbe2::tree::Node>((*_write)->v_mut())
               .a0;
      _loop_acc = a0(_loop_acc);
      _loop_fs = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_head);
}

uint64_t MemSafetyProbe2::apply_all(
    const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> &fs,
    uint64_t x) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> *fs;
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
      const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> &fs = *_f.fs;
      if (std::holds_alternative<typename MemSafetyProbe2::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(fs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe2::mylist<
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
