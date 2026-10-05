#include "mem_safety_probe2.h"

/// TEST 7: Closure escaping through a list, then applied.
MemSafetyProbe2::mylist<uint64_t> MemSafetyProbe2::map_apply(
    const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> &fs,
    uint64_t x) {
  std::optional<MemSafetyProbe2::mylist<uint64_t>> _root{};
  std::shared_ptr<MemSafetyProbe2::mylist<uint64_t>> *_write = nullptr;
  const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> *_loop_fs = &fs;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe2::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mynil>(_loop_fs->v())) {
      auto _value = mylist<uint64_t>::mynil();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe2::mylist<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<typename MemSafetyProbe2::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>(_loop_fs->v());
      auto _cell =
          typename MemSafetyProbe2::mylist<uint64_t>::Mycons(a0(x), nullptr);
      MemSafetyProbe2::mylist<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<MemSafetyProbe2::mylist<uint64_t>>(
                              std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename MemSafetyProbe2::mylist<uint64_t>::Mycons>(
                    _node.v_mut())
                    .a1;
      _loop_fs = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe2::mysum(const MemSafetyProbe2::mylist<uint64_t> &l) {
  {
    const MemSafetyProbe2::mylist<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const MemSafetyProbe2::mylist<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<
              typename MemSafetyProbe2::mylist<uint64_t>::Mynil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe2::mylist<uint64_t>::Mycons>(
                _lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

/// TEST 13: Fold building tree from closures' results.
MemSafetyProbe2::tree MemSafetyProbe2::fold_tree_build(
    const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> &fs,
    uint64_t acc) {
  std::optional<MemSafetyProbe2::tree> _root{};
  std::shared_ptr<MemSafetyProbe2::tree> *_write = nullptr;
  uint64_t _loop_acc = acc;
  const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> *_loop_fs = &fs;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe2::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mynil>(_loop_fs->v())) {
      auto _value = tree::leaf();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe2::tree>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<typename MemSafetyProbe2::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>(_loop_fs->v());
      auto _cell = typename MemSafetyProbe2::tree::Node(
          nullptr, a0(_loop_acc),
          std::make_shared<MemSafetyProbe2::tree>(tree::leaf()));
      MemSafetyProbe2::tree &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe2::tree>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe2::tree::Node>(_node.v_mut()).a0;
      _loop_acc = a0(_loop_acc);
      _loop_fs = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
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
