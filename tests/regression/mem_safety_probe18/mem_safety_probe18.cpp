#include "mem_safety_probe18.h"

uint64_t
MemSafetyProbe18::sum_list(const MemSafetyProbe18::mylist<uint64_t> &l) {
  {
    const MemSafetyProbe18::mylist<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const MemSafetyProbe18::mylist<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<
              typename MemSafetyProbe18::mylist<uint64_t>::Mynil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe18::mylist<uint64_t>::Mycons>(
                _lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

/// TEST 5: Complex fold that builds a tree from a list.
MemSafetyProbe18::tree
MemSafetyProbe18::fold_left_tree(const MemSafetyProbe18::mylist<uint64_t> &l,
                                 MemSafetyProbe18::tree acc) {
  MemSafetyProbe18::tree _loop_acc = std::move(acc);
  const MemSafetyProbe18::mylist<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe18::mylist<uint64_t>::Mynil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe18::mylist<uint64_t>::Mycons>(
              _loop_l->v());
      _loop_acc = tree::node(std::move(_loop_acc), a0, tree::leaf());
      _loop_l = crane_raw(a1);
    }
  }
}

/// TEST 8: Nested constructor building: build a list of trees
/// using the same tree in different positions.
MemSafetyProbe18::mylist<MemSafetyProbe18::tree>
MemSafetyProbe18::build_tree_list(const MemSafetyProbe18::tree &t, uint64_t n) {
  std::optional<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>> _root{};
  std::shared_ptr<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>> *_write =
      nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = mylist<MemSafetyProbe18::tree>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe18::mylist<MemSafetyProbe18::tree>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell =
          typename MemSafetyProbe18::mylist<MemSafetyProbe18::tree>::Mycons(
              tree::node(t, _loop_n, tree::leaf()), nullptr);
      MemSafetyProbe18::mylist<MemSafetyProbe18::tree> &_node =
          (_write ? *(*_write = std::make_shared<
                          MemSafetyProbe18::mylist<MemSafetyProbe18::tree>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename MemSafetyProbe18::mylist<
          MemSafetyProbe18::tree>::Mycons>(_node.v_mut())
                    .a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe18::sum_tree_list(
    const MemSafetyProbe18::mylist<MemSafetyProbe18::tree>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const MemSafetyProbe18::mylist<MemSafetyProbe18::tree> *l;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    MemSafetyProbe18::tree a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified sum_tree_list: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe18::mylist<MemSafetyProbe18::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe18::mylist<MemSafetyProbe18::tree>::Mynil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe18::mylist<MemSafetyProbe18::tree>::Mycons>(
            l.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      MemSafetyProbe18::tree a0 = std::move(_f.a0);
      _result = (a0.tree_sum() + std::move(_result));
    }
  }
  return _result;
}
