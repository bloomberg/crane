#include "mem_safety_probe16.h"

uint64_t
MemSafetyProbe16::sum_list(const MemSafetyProbe16::mylist<uint64_t> &l) {
  {
    const MemSafetyProbe16::mylist<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const MemSafetyProbe16::mylist<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<
              typename MemSafetyProbe16::mylist<uint64_t>::Mynil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe16::mylist<uint64_t>::Mycons>(
                _lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe16::build_summers(
    const MemSafetyProbe16::mylist<MemSafetyProbe16::tree> &trees) {
  std::optional<MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>>>
      _root{};
  std::shared_ptr<MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>>>
      *_write = nullptr;
  MemSafetyProbe16::mylist<MemSafetyProbe16::tree> _loop_trees = trees;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe16::mylist<MemSafetyProbe16::tree>::Mynil>(
            _loop_trees.v())) {
      auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe16::mylist<MemSafetyProbe16::tree>::Mycons>(
          _loop_trees.v());
      const MemSafetyProbe16::mylist<MemSafetyProbe16::tree> &a1_value = *a1;
      auto _cell = typename MemSafetyProbe16::
          mylist<crane::fn<uint64_t(uint64_t)>>::Mycons(
              [=](uint64_t _x0) -> uint64_t { return a0.make_summer(_x0); },
              nullptr);
      MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>> &_node =
          (_write
               ? *(*_write = std::make_shared<
                       MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>>>(
                       std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename MemSafetyProbe16::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>(_node.v_mut())
                    .a1;
      _loop_trees = a1_value;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe16::apply_fns(
    const MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>> &fns,
    uint64_t x) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    const MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>> *fns;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&fns});
  /// Loopified apply_fns: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>> &fns =
          *_f.fns;
      if (std::holds_alternative<typename MemSafetyProbe16::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe16::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(fns.v());
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

/// TEST 3: Build a list of closures where each closure captures
/// the SAME tree at different levels.
/// Tests whether the tree is properly cloned for each closure.
MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe16::multi_capture_tree(MemSafetyProbe16::tree t, uint64_t n) {
  std::optional<MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>>>
      _root{};
  std::shared_ptr<MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>>>
      *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell =
          typename MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>>::
              Mycons([=](uint64_t x) { return ((t.tree_sum() + x) + _loop_n); },
                     nullptr);
      MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>> &_node =
          (_write
               ? *(*_write = std::make_shared<
                       MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>>>(
                       std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write = &std::get<typename MemSafetyProbe16::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>(_node.v_mut())
                    .a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

/// TEST 4: Return a closure from inside a NESTED match.
/// The closure captures bindings from BOTH match levels.
uint64_t MemSafetyProbe16::nested_match_closure(
    const MemSafetyProbe16::tree &t,
    const MemSafetyProbe16::mylist<uint64_t> &l, uint64_t n) {
  if (std::holds_alternative<typename MemSafetyProbe16::tree::Leaf>(t.v())) {
    return n;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe16::tree::Node>(t.v());
    if (std::holds_alternative<
            typename MemSafetyProbe16::mylist<uint64_t>::Mynil>(l.v())) {
      return (a1 + n);
    } else {
      const auto &[a00, a10] =
          std::get<typename MemSafetyProbe16::mylist<uint64_t>::Mycons>(l.v());
      return ((((a0->tree_sum() + a2->tree_sum()) + a1) + a00) + n);
    }
  }
}

/// TEST 7: Map + apply pattern: build closures from tree children,
/// apply them to values from another list.
MemSafetyProbe16::mylist<uint64_t> MemSafetyProbe16::zip_apply(
    const MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>> &fns,
    const MemSafetyProbe16::mylist<uint64_t> &vals) {
  std::optional<MemSafetyProbe16::mylist<uint64_t>> _root{};
  std::shared_ptr<MemSafetyProbe16::mylist<uint64_t>> *_write = nullptr;
  const MemSafetyProbe16::mylist<uint64_t> *_loop_vals = &vals;
  const MemSafetyProbe16::mylist<crane::fn<uint64_t(uint64_t)>> *_loop_fns =
      &fns;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe16::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mynil>(_loop_fns->v())) {
      auto _value = mylist<uint64_t>::mynil();
      (_write
           ? *(*_write = std::make_shared<MemSafetyProbe16::mylist<uint64_t>>(
                   std::move(_value)))
           : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<typename MemSafetyProbe16::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>(_loop_fns->v());
      if (std::holds_alternative<
              typename MemSafetyProbe16::mylist<uint64_t>::Mynil>(
              _loop_vals->v())) {
        auto _value = mylist<uint64_t>::mynil();
        (_write
             ? *(*_write = std::make_shared<MemSafetyProbe16::mylist<uint64_t>>(
                     std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename MemSafetyProbe16::mylist<uint64_t>::Mycons>(
                _loop_vals->v());
        auto _cell = typename MemSafetyProbe16::mylist<uint64_t>::Mycons(
            a0(a00), nullptr);
        MemSafetyProbe16::mylist<uint64_t> &_node =
            (_write
                 ? *(*_write =
                         std::make_shared<MemSafetyProbe16::mylist<uint64_t>>(
                             std::move(_cell)))
                 : _root.emplace(std::move(_cell)));
        _write = &std::get<typename MemSafetyProbe16::mylist<uint64_t>::Mycons>(
                      _node.v_mut())
                      .a1;
        _loop_vals = crane_raw(a10);
        _loop_fns = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

MemSafetyProbe16::mylist<uint64_t>
MemSafetyProbe16::flatten_cps(const MemSafetyProbe16::tree &t) {
  return flatten_cps_aux(
      t, [](MemSafetyProbe16::mylist<uint64_t> x) { return x; });
}
