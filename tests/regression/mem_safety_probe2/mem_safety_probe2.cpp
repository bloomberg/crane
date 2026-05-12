#include "mem_safety_probe2.h"

/// TEST 7: Closure escaping through a list, then applied.
MemSafetyProbe2::mylist<unsigned int> MemSafetyProbe2::map_apply(
    const MemSafetyProbe2::mylist<std::function<unsigned int(unsigned int)>>
        &fs,
    const unsigned int x) {
  std::unique_ptr<MemSafetyProbe2::mylist<unsigned int>> _head{};
  std::unique_ptr<MemSafetyProbe2::mylist<unsigned int>> *_write = &_head;
  const MemSafetyProbe2::mylist<std::function<unsigned int(unsigned int)>>
      *_loop_fs = &fs;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe2::mylist<
            std::function<unsigned int(unsigned int)>>::Mynil>(_loop_fs->v())) {
      *(_write) = std::make_unique<MemSafetyProbe2::mylist<unsigned int>>(
          mylist<unsigned int>::mynil());
      break;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe2::mylist<
          std::function<unsigned int(unsigned int)>>::Mycons>(_loop_fs->v());
      auto _cell = std::make_unique<MemSafetyProbe2::mylist<unsigned int>>(
          typename mylist<unsigned int>::Mycons(d_a0(x), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename mylist<unsigned int>::Mycons>((*_write)->v_mut())
               .d_a1;
      _loop_fs = d_a1.get();
      continue;
    }
  }
  return std::move(*(_head));
}

unsigned int MemSafetyProbe2::mysum(
    const MemSafetyProbe2::mylist<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe2::mylist<unsigned int> *l;
  };

  /// _Resume_Mycons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter(&l));
  /// Loopified mysum: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe2::mylist<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename MemSafetyProbe2::mylist<unsigned int>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename MemSafetyProbe2::mylist<unsigned int>::Mycons>(
                l.v());
        _stack.emplace_back(_Resume_Mycons(d_a0));
        _stack.emplace_back(_Enter(d_a1.get()));
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.d_a0 + _result);
    }
  }
  return _result;
}

/// TEST 13: Fold building tree from closures' results.
MemSafetyProbe2::tree MemSafetyProbe2::fold_tree_build(
    const MemSafetyProbe2::mylist<std::function<unsigned int(unsigned int)>>
        &fs,
    const unsigned int acc) {
  std::unique_ptr<MemSafetyProbe2::tree> _head{};
  std::unique_ptr<MemSafetyProbe2::tree> *_write = &_head;
  unsigned int _loop_acc = acc;
  const MemSafetyProbe2::mylist<std::function<unsigned int(unsigned int)>>
      *_loop_fs = &fs;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe2::mylist<
            std::function<unsigned int(unsigned int)>>::Mynil>(_loop_fs->v())) {
      *(_write) = std::make_unique<MemSafetyProbe2::tree>(tree::leaf());
      break;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe2::mylist<
          std::function<unsigned int(unsigned int)>>::Mycons>(_loop_fs->v());
      auto _cell = std::make_unique<MemSafetyProbe2::tree>(typename tree::Node(
          nullptr, d_a0(_loop_acc),
          std::make_unique<MemSafetyProbe2::tree>(tree::leaf())));
      *(_write) = std::move(_cell);
      _write = &std::get<typename tree::Node>((*_write)->v_mut()).d_a0;
      _loop_acc = d_a0(_loop_acc);
      _loop_fs = d_a1.get();
      continue;
    }
  }
  return std::move(*(_head));
}

unsigned int MemSafetyProbe2::apply_all(
    const MemSafetyProbe2::mylist<std::function<unsigned int(unsigned int)>>
        &fs,
    const unsigned int
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe2::mylist<std::function<unsigned int(unsigned int)>>
        *fs;
  };

  /// _Resume_Mycons: saves [x], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int x;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter(&fs));
  /// Loopified apply_all: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe2::mylist<std::function<unsigned int(unsigned int)>>
          &fs = *(_f.fs);
      if (std::holds_alternative<typename MemSafetyProbe2::mylist<
              std::function<unsigned int(unsigned int)>>::Mynil>(fs.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe2::mylist<
            std::function<unsigned int(unsigned int)>>::Mycons>(fs.v());
        _stack.emplace_back(_Resume_Mycons(d_a0(x)));
        _stack.emplace_back(_Enter(d_a1.get()));
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.x + _result);
    }
  }
  return _result;
}
