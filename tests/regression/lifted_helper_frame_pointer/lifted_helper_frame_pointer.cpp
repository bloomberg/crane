#include "lifted_helper_frame_pointer.h"

/// Each leaf of a counts 1 where the tree passed beside it is a node.
/// Used at two types, the fixpoint stays polymorphic, and is lifted.
uint64_t LiftedHelperFramePointer::zigzag(
    const LiftedHelperFramePointer::tree<uint64_t> &t,
    const LiftedHelperFramePointer::tree<uint64_t> &u,
    const LiftedHelperFramePointer::tree<bool> &s,
    const LiftedHelperFramePointer::tree<bool> &w) {
  return (zigzag_crane_go(t, u) + (UINT64_C(1000) * zigzag_crane_go(s, w)));
}

LiftedHelperFramePointer::tree<bool> LiftedHelperFramePointer::full_bool(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_k: saves [k], resumes after recursive call, then processes rest.
  struct CraneCont_k {
    uint64_t k;
  };

  /// CraneCont_k_1: saves [k, _tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_k_1 {
    uint64_t k;
    LiftedHelperFramePointer::tree<bool> _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_k, CraneCont_k_1>;
  LiftedHelperFramePointer::tree<bool> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified full_bool: CraneEnter -> CraneCont_k -> CraneCont_k_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree<bool>::leaf();
      } else {
        uint64_t k = n - 1;
        _stack.emplace_back(CraneCont_k{k});
        _stack.emplace_back(CraneEnter{k});
      }
    } else if (std::holds_alternative<CraneCont_k>(_frame)) {
      auto _f = std::move(std::get<CraneCont_k>(_frame));
      uint64_t k = _f.k;
      _stack.emplace_back(CraneCont_k_1{k, std::move(_result)});
      _stack.emplace_back(CraneEnter{k});
    } else {
      auto _f = std::move(std::get<CraneCont_k_1>(_frame));
      uint64_t k = _f.k;
      _result = tree<bool>::node(std::move(_f._tmp2), Nat::even(k),
                                 std::move(_result));
    }
  }
  return _result;
}

LiftedHelperFramePointer::tree<uint64_t>
LiftedHelperFramePointer::spine(uint64_t n) {
  std::optional<LiftedHelperFramePointer::tree<uint64_t>> _root{};
  std::shared_ptr<LiftedHelperFramePointer::tree<uint64_t>> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = tree<uint64_t>::leaf();
      (_write
           ? *(*_write =
                   std::make_shared<LiftedHelperFramePointer::tree<uint64_t>>(
                       std::move(_value)))
           : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t k = _loop_n - 1;
      auto _cell = typename LiftedHelperFramePointer::tree<uint64_t>::Node(
          std::make_shared<LiftedHelperFramePointer::tree<uint64_t>>(
              tree<uint64_t>::leaf()),
          k, nullptr);
      LiftedHelperFramePointer::tree<uint64_t> &_node =
          (_write ? *(*_write = std::make_shared<
                          LiftedHelperFramePointer::tree<uint64_t>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LiftedHelperFramePointer::tree<uint64_t>::Node>(
               _node.v_mut())
               .a2;
      _loop_n = k;
      continue;
    }
  }
  return std::move(*_root);
}

LiftedHelperFramePointer::tree<uint64_t> LiftedHelperFramePointer::full(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_k: saves [k], resumes after recursive call, then processes rest.
  struct CraneCont_k {
    uint64_t k;
  };

  /// CraneCont_k_1: saves [k, _tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_k_1 {
    uint64_t k;
    LiftedHelperFramePointer::tree<uint64_t> _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_k, CraneCont_k_1>;
  LiftedHelperFramePointer::tree<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified full: CraneEnter -> CraneCont_k -> CraneCont_k_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree<uint64_t>::leaf();
      } else {
        uint64_t k = n - 1;
        _stack.emplace_back(CraneCont_k{k});
        _stack.emplace_back(CraneEnter{k});
      }
    } else if (std::holds_alternative<CraneCont_k>(_frame)) {
      auto _f = std::move(std::get<CraneCont_k>(_frame));
      uint64_t k = _f.k;
      _stack.emplace_back(CraneCont_k_1{k, std::move(_result)});
      _stack.emplace_back(CraneEnter{k});
    } else {
      auto _f = std::move(std::get<CraneCont_k_1>(_frame));
      uint64_t k = _f.k;
      _result =
          tree<uint64_t>::node(std::move(_f._tmp2), k, std::move(_result));
    }
  }
  return _result;
}

bool Nat::even(uint64_t n) {
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return true;
    } else {
      uint64_t n0 = _loop_n - 1;
      if (n0 <= 0) {
        return false;
      } else {
        uint64_t n_ = n0 - 1;
        _loop_n = n_;
      }
    }
  }
}
