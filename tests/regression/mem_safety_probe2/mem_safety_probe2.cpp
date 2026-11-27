#include "mem_safety_probe2.h"

/// TEST 7: Closure escaping through a list, then applied.
MemSafetyProbe2::mylist<uint64_t> MemSafetyProbe2::map_apply(
    const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> &fs,
    uint64_t x) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
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
      _write =
          &std::get<typename MemSafetyProbe2::mylist<uint64_t>::Mycons>(
              _node.v_mut())
              .a1;
      _loop_fs = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe2::mysum(const MemSafetyProbe2::mylist<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of mysum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe2::mylist<uint64_t> *l;
  };

  struct _after_mysum_in_Mycons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_mysum_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe2::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe2::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe2::mylist<uint64_t>::Mycons>(l.v());
        _stack.emplace_back(_after_mysum_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_mysum_in_Mycons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + _result);
    }
  }
  return _result;
}

/// TEST 13: Fold building tree from closures' results.
MemSafetyProbe2::tree MemSafetyProbe2::fold_tree_build(
    const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> &fs,
    uint64_t acc) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe2::tree> _root{};
  std::shared_ptr<MemSafetyProbe2::tree> *_write = nullptr;
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
          nullptr, a0(acc),
          std::make_shared<MemSafetyProbe2::tree>(tree::leaf()));
      MemSafetyProbe2::tree &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe2::tree>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe2::tree::Node>(_node.v_mut()).a0;
      acc = a0(acc);
      _loop_fs = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe2::apply_all(
    const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> &fs,
    uint64_t x) {
  // Explicit stack replaces the non-tail recursion of apply_all: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> *fs;
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
      const MemSafetyProbe2::mylist<crane::fn<uint64_t(uint64_t)>> &fs = *_f.fs;
      if (std::holds_alternative<typename MemSafetyProbe2::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(fs.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe2::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(fs.v());
        _stack.emplace_back(_after_apply_all_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_apply_all_in_Mycons>(_popped));
      _stack.pop_back();
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      _result = (a0(x) + _result);
    }
  }
  return _result;
}
