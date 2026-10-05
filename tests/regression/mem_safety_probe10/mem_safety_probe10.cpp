#include "mem_safety_probe10.h"

uint64_t MemSafetyProbe10::sum_fns(
    const MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>> *l;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified sum_fns: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>> &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe10::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe10::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      _result = (a0(UINT64_C(0)) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 3: Recursive function returning a list of closures.
/// Each closure captures the tree node's value and subtrees.
MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe10::collect_adders(const MemSafetyProbe10::tree &t) {
  std::optional<MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>>
      _root{};
  std::shared_ptr<MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>>
      *_write = nullptr;
  MemSafetyProbe10::tree _loop_t = t;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe10::tree::Leaf>(
            _loop_t.v())) {
      auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1, a2] =
          std::get<typename MemSafetyProbe10::tree::Node>(_loop_t.v());
      const MemSafetyProbe10::tree &a0_value = *a0;
      const MemSafetyProbe10::tree &a2_value = *a2;
      auto _cell1 = std::make_shared<
          MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>>(
          typename MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>::
              Mycons([=](uint64_t n) { return (a0_value.tree_sum() + n); },
                     nullptr));
      auto _cell2 = std::make_shared<
          MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>>(
          typename MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>::
              Mycons([=](uint64_t n) { return (a2_value.tree_sum() + n); },
                     nullptr));
      std::get<typename MemSafetyProbe10::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons>(_cell1->v_mut())
          .a1 = std::move(_cell2);
      auto _cell =
          typename MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>::
              Mycons([=](uint64_t n) { return (a1 + n); }, std::move(_cell1));
      MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>> &_node =
          (_write
               ? *(*_write = std::make_shared<
                       MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>>(
                       std::move(_cell)))
               : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe10::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mycons>(
               std::get<typename MemSafetyProbe10::mylist<
                   crane::fn<uint64_t(uint64_t)>>::Mycons>(
                   std::get<typename MemSafetyProbe10::mylist<
                       crane::fn<uint64_t(uint64_t)>>::Mycons>(_node.v_mut())
                       .a1->v_mut())
                   .a1->v_mut())
               .a1;
      _loop_t = a0_value;
      continue;
    }
  }
  return std::move(*_root);
}

/// TEST 4: Closure returned from nested match.
/// Tests return_captures_by_value through Sif branches.
uint64_t MemSafetyProbe10::choose_fn(const std::optional<bool> &o, uint64_t v,
                                     uint64_t n) {
  if (o.has_value()) {
    const bool &b = *o;
    if (b) {
      return (v + n);
    } else {
      return (v * n);
    }
  } else {
    return n;
  }
}

/// TEST 6: Function returning closure in pair.
/// Tests pair construction with closure.
std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe10::pair_with_fn(uint64_t n) {
  return std::make_pair([=](uint64_t x) { return (n + x); }, (n * UINT64_C(2)));
}

/// TEST 7: Mutually recursive functions using a fixpoint
/// where one captures the other's result as a closure.
MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe10::build_tree_fns(const MemSafetyProbe10::tree &t,
                                 uint64_t depth) {
  std::optional<MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>>
      _root{};
  std::shared_ptr<MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>>
      *_write = nullptr;
  uint64_t _loop_depth = std::move(depth);
  MemSafetyProbe10::tree _loop_t = t;
  while (true) {
    if (_loop_depth <= 0) {
      auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t d = _loop_depth - 1;
      if (std::holds_alternative<typename MemSafetyProbe10::tree::Leaf>(
              _loop_t.v())) {
        auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
            [](uint64_t n) { return n; },
            mylist<crane::fn<uint64_t(uint64_t)>>::mynil());
        (_write
             ? *(*_write = std::make_shared<
                     MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>>(
                     std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe10::tree::Node>(_loop_t.v());
        const MemSafetyProbe10::tree &a0_value = *a0;
        const MemSafetyProbe10::tree &a2_value = *a2;
        auto _cell1 = std::make_shared<
            MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>>(
            typename MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>::
                Mycons(
                    [=](uint64_t n) {
                      return ((a0_value.tree_sum() + a2_value.tree_sum()) + n);
                    },
                    nullptr));
        auto _cell =
            typename MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>>::
                Mycons([=](uint64_t n) { return (a1 + n); }, std::move(_cell1));
        MemSafetyProbe10::mylist<crane::fn<uint64_t(uint64_t)>> &_node =
            (_write ? *(*_write = std::make_shared<MemSafetyProbe10::mylist<
                            crane::fn<uint64_t(uint64_t)>>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename MemSafetyProbe10::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(
                      std::get<typename MemSafetyProbe10::mylist<
                          crane::fn<uint64_t(uint64_t)>>::Mycons>(_node.v_mut())
                          .a1->v_mut())
                      .a1;
        _loop_depth = d;
        _loop_t = a0_value;
        continue;
      }
    }
  }
  return std::move(*_root);
}
