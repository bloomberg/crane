#include "mem_safety_probe16.h"

unsigned int MemSafetyProbe16::sum_list(
    const MemSafetyProbe16::mylist<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe16::mylist<unsigned int> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe16::mylist<unsigned int> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe16::mylist<unsigned int>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe16::mylist<unsigned int>::Mycons>(
                l.v());
        _stack.emplace_back(_Resume_Mycons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.a0 + _result);
    }
  }
  return _result;
}

MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe16::build_summers(
    const MemSafetyProbe16::mylist<MemSafetyProbe16::tree> &trees) {
  std::unique_ptr<
      MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>>
      _head{};
  std::unique_ptr<
      MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>>
      *_write = &_head;
  MemSafetyProbe16::mylist<MemSafetyProbe16::tree> _loop_trees = trees;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe16::mylist<MemSafetyProbe16::tree>::Mynil>(
            _loop_trees.v())) {
      *_write = std::make_unique<
          MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>>(
          mylist<std::function<unsigned int(unsigned int)>>::mynil());
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe16::mylist<MemSafetyProbe16::tree>::Mycons>(
          _loop_trees.v());
      MemSafetyProbe16::mylist<MemSafetyProbe16::tree> a1_value = *a1;
      auto _cell = std::make_unique<
          MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>>(
          typename mylist<std::function<unsigned int(unsigned int)>>::Mycons(
              [=](unsigned int _x0) mutable -> unsigned int {
                return a0.make_summer(_x0);
              },
              nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename mylist<
          std::function<unsigned int(unsigned int)>>::Mycons>(
                    (*_write)->v_mut())
                    .a1;
      _loop_trees = a1_value;
      continue;
    }
  }
  return std::move(*_head);
}

unsigned int MemSafetyProbe16::apply_fns(
    const MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    unsigned int
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>
        *fns;
  };

  /// _Resume_Mycons: saves [x], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int x;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&fns});
  /// Loopified apply_fns: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>
          &fns = *_f.fns;
      if (std::holds_alternative<typename MemSafetyProbe16::mylist<
              std::function<unsigned int(unsigned int)>>::Mynil>(fns.v())) {
        _result = 0u;
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe16::mylist<
            std::function<unsigned int(unsigned int)>>::Mycons>(fns.v());
        _stack.emplace_back(_Resume_Mycons{a0(x)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.x + _result);
    }
  }
  return _result;
}

/// TEST 3: Build a list of closures where each closure captures
/// the SAME tree at different levels.
/// Tests whether the tree is properly cloned for each closure.
MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe16::multi_capture_tree(MemSafetyProbe16::tree t, unsigned int n) {
  std::unique_ptr<
      MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>>
      _head{};
  std::unique_ptr<
      MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>>
      *_write = &_head;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<
          MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>>(
          mylist<std::function<unsigned int(unsigned int)>>::mynil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = std::make_unique<
          MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>>(
          typename mylist<std::function<unsigned int(unsigned int)>>::Mycons(
              [=](unsigned int x) mutable {
                return ((t.tree_sum() + x) + _loop_n);
              },
              nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename mylist<
          std::function<unsigned int(unsigned int)>>::Mycons>(
                    (*_write)->v_mut())
                    .a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

/// TEST 4: Return a closure from inside a NESTED match.
/// The closure captures bindings from BOTH match levels.
unsigned int MemSafetyProbe16::nested_match_closure(
    const MemSafetyProbe16::tree &t,
    const MemSafetyProbe16::mylist<unsigned int> &l, unsigned int n) {
  if (std::holds_alternative<typename MemSafetyProbe16::tree::Leaf>(t.v())) {
    return n;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe16::tree::Node>(t.v());
    if (std::holds_alternative<
            typename MemSafetyProbe16::mylist<unsigned int>::Mynil>(l.v())) {
      return (a1 + n);
    } else {
      const auto &[a00, a10] =
          std::get<typename MemSafetyProbe16::mylist<unsigned int>::Mycons>(
              l.v());
      return (((((*a0).tree_sum() + (*a2).tree_sum()) + a1) + a00) + n);
    }
  }
}

/// TEST 7: Map + apply pattern: build closures from tree children,
/// apply them to values from another list.
MemSafetyProbe16::mylist<unsigned int> MemSafetyProbe16::zip_apply(
    const MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    const MemSafetyProbe16::mylist<unsigned int> &vals) {
  std::unique_ptr<MemSafetyProbe16::mylist<unsigned int>> _head{};
  std::unique_ptr<MemSafetyProbe16::mylist<unsigned int>> *_write = &_head;
  const MemSafetyProbe16::mylist<unsigned int> *_loop_vals = &vals;
  const MemSafetyProbe16::mylist<std::function<unsigned int(unsigned int)>>
      *_loop_fns = &fns;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe16::mylist<
            std::function<unsigned int(unsigned int)>>::Mynil>(
            _loop_fns->v())) {
      *_write = std::make_unique<MemSafetyProbe16::mylist<unsigned int>>(
          mylist<unsigned int>::mynil());
      break;
    } else {
      const auto &[a0, a1] = std::get<typename MemSafetyProbe16::mylist<
          std::function<unsigned int(unsigned int)>>::Mycons>(_loop_fns->v());
      if (std::holds_alternative<
              typename MemSafetyProbe16::mylist<unsigned int>::Mynil>(
              _loop_vals->v())) {
        *_write = std::make_unique<MemSafetyProbe16::mylist<unsigned int>>(
            mylist<unsigned int>::mynil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename MemSafetyProbe16::mylist<unsigned int>::Mycons>(
                _loop_vals->v());
        auto _cell = std::make_unique<MemSafetyProbe16::mylist<unsigned int>>(
            typename mylist<unsigned int>::Mycons(a0(a00), nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename mylist<unsigned int>::Mycons>((*_write)->v_mut())
                 .a1;
        _loop_vals = a10.get();
        _loop_fns = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

MemSafetyProbe16::mylist<unsigned int>
MemSafetyProbe16::flatten_cps(const MemSafetyProbe16::tree &t) {
  return flatten_cps_aux(
      t, [](MemSafetyProbe16::mylist<unsigned int> x) { return x; });
}
