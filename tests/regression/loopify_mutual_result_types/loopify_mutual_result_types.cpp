#include "loopify_mutual_result_types.h"

/// dbl_e and dbl_md are mutually recursive and return different types
/// (e and md).  With Set Crane Loopify, dbl_e becomes a frame-stack
/// loop that inlines dbl_md as extra frames (_Enter_inl), but both halves
/// store into the one _result variable, declared at dbl_e's result type:
/// _result = Md::mnull(); assigns an md to an e -- "no viable
/// overloaded '='" -- and the resume frame then hands that _result to a
/// constructor expecting the other type.
///
/// Found in Vellvm with the global Set Crane Loopify:
/// Traversal.ft_exp / ft_metadata, 4 of its 59 errors.
LoopifyMutualResultTypes::e
LoopifyMutualResultTypes::dbl_e(const LoopifyMutualResultTypes::e &
                                    x) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyMutualResultTypes::e *x;
  };

  /// CraneCont_Add: saves [b0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Add {
    const LoopifyMutualResultTypes::e *b0;
  };

  /// CraneCont_Add_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Add_1 {
    LoopifyMutualResultTypes::e _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1>;
  LoopifyMutualResultTypes::e _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&x});
  /// Loopified dbl_e: CraneEnter -> CraneCont_Add -> CraneCont_Add_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyMutualResultTypes::e &x = *_f.x;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
              x.v())) {
        const auto &[n0] =
            std::get<typename LoopifyMutualResultTypes::e::Leaf>(x.v());
        _result = e::leaf((UINT64_C(2) * n0));
      } else if (std::holds_alternative<
                     typename LoopifyMutualResultTypes::e::Add>(x.v())) {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::e::Add>(x.v());
        _stack.emplace_back(CraneCont_Add{crane_raw(b0)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      } else {
        const auto &[m0] =
            std::get<typename LoopifyMutualResultTypes::e::Meta>(x.v());
        _result = e::meta([](const LoopifyMutualResultTypes::md &_inl_m)
                              -> LoopifyMutualResultTypes::md {
          if (std::holds_alternative<
                  typename LoopifyMutualResultTypes::md::MNull>(_inl_m.v())) {
            return md::mnull();
          } else if (std::holds_alternative<
                         typename LoopifyMutualResultTypes::md::MConst>(
                         _inl_m.v())) {
            const auto &[_inl_x0] =
                std::get<typename LoopifyMutualResultTypes::md::MConst>(
                    _inl_m.v());
            return md::mconst(dbl_e(*_inl_x0));
          } else {
            const auto &[_inl_a0, _inl_b0] =
                std::get<typename LoopifyMutualResultTypes::md::MPair>(
                    _inl_m.v());
            return md::mpair(dbl_md(*_inl_a0), dbl_md(*_inl_b0));
          }
        }(*m0));
      }
    } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Add>(_frame));
      const LoopifyMutualResultTypes::e &b0 = *_f.b0;
      _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&b0});
    } else {
      auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
      _result = e::add(std::move(_f._tmp2), std::move(_result));
    }
  }
  return _result;
}

LoopifyMutualResultTypes::md LoopifyMutualResultTypes::dbl_md(
    const LoopifyMutualResultTypes::md
        &m) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyMutualResultTypes::md *m;
  };

  /// CraneCont_MPair: saves [b0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_MPair {
    const LoopifyMutualResultTypes::md *b0;
  };

  /// CraneCont_MPair_1: saves [_tmp3], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_MPair_1 {
    LoopifyMutualResultTypes::md _tmp3;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont_MPair, CraneCont_MPair_1>;
  LoopifyMutualResultTypes::md _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&m});
  /// Loopified dbl_md: CraneEnter -> CraneCont_MPair -> CraneCont_MPair_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyMutualResultTypes::md &m = *_f.m;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::md::MNull>(
              m.v())) {
        _result = md::mnull();
      } else if (std::holds_alternative<
                     typename LoopifyMutualResultTypes::md::MConst>(m.v())) {
        const auto &[x0] =
            std::get<typename LoopifyMutualResultTypes::md::MConst>(m.v());
        _result = md::mconst([](const LoopifyMutualResultTypes::e &_inl_x)
                                 -> LoopifyMutualResultTypes::e {
          if (std::holds_alternative<
                  typename LoopifyMutualResultTypes::e::Leaf>(_inl_x.v())) {
            const auto &[_inl_n0] =
                std::get<typename LoopifyMutualResultTypes::e::Leaf>(
                    _inl_x.v());
            return e::leaf((UINT64_C(2) * _inl_n0));
          } else if (std::holds_alternative<
                         typename LoopifyMutualResultTypes::e::Add>(
                         _inl_x.v())) {
            const auto &[_inl_a0, _inl_b0] =
                std::get<typename LoopifyMutualResultTypes::e::Add>(_inl_x.v());
            return e::add(dbl_e(*_inl_a0), dbl_e(*_inl_b0));
          } else {
            const auto &[_inl_m0] =
                std::get<typename LoopifyMutualResultTypes::e::Meta>(
                    _inl_x.v());
            return e::meta(dbl_md(*_inl_m0));
          }
        }(*x0));
      } else {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::md::MPair>(m.v());
        _stack.emplace_back(CraneCont_MPair{crane_raw(b0)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_MPair>(_frame)) {
      auto _f = std::move(std::get<CraneCont_MPair>(_frame));
      const LoopifyMutualResultTypes::md &b0 = *_f.b0;
      _stack.emplace_back(CraneCont_MPair_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&b0});
    } else {
      auto _f = std::move(std::get<CraneCont_MPair_1>(_frame));
      _result = md::mpair(std::move(_f._tmp3), std::move(_result));
    }
  }
  return _result;
}

uint64_t
LoopifyMutualResultTypes::sum_e(const LoopifyMutualResultTypes::e &
                                    x) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    const LoopifyMutualResultTypes::e *x;
  };

  /// CraneCont_Add: saves [b0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Add {
    const LoopifyMutualResultTypes::e *b0;
  };

  /// CraneCont_Add_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Add_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&x});
  /// Loopified sum_e: CraneEnter -> CraneCont_Add -> CraneCont_Add_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyMutualResultTypes::e &x = *_f.x;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
              x.v())) {
        const auto &[n0] =
            std::get<typename LoopifyMutualResultTypes::e::Leaf>(x.v());
        _result = std::move(n0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualResultTypes::e::Add>(x.v())) {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::e::Add>(x.v());
        _stack.emplace_back(CraneCont_Add{crane_raw(b0)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      } else {
        const auto &[m0] =
            std::get<typename LoopifyMutualResultTypes::e::Meta>(x.v());
        const LoopifyMutualResultTypes::md &_inl_m = *m0;
        if (std::holds_alternative<
                typename LoopifyMutualResultTypes::md::MNull>(_inl_m.v())) {
          _result = UINT64_C(0);
        } else if (std::holds_alternative<
                       typename LoopifyMutualResultTypes::md::MConst>(
                       _inl_m.v())) {
          const auto &[_inl_x0] =
              std::get<typename LoopifyMutualResultTypes::md::MConst>(
                  _inl_m.v());
          _stack.emplace_back(CraneEnter{crane_raw(_inl_x0)});
        } else {
          const auto &[_inl_a0, _inl_b0] =
              std::get<typename LoopifyMutualResultTypes::md::MPair>(
                  _inl_m.v());
          _result = (sum_md(*_inl_a0) + sum_md(*_inl_b0));
        }
      }
    } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Add>(_frame));
      const LoopifyMutualResultTypes::e &b0 = *_f.b0;
      _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&b0});
    } else {
      auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyMutualResultTypes::sum_md(
    const LoopifyMutualResultTypes::md
        &m) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifyMutualResultTypes::md *m;
  };

  /// CraneCont_MPair: saves [b0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_MPair {
    const LoopifyMutualResultTypes::md *b0;
  };

  /// CraneCont_MPair_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_MPair_1 {
    uint64_t _tmp2;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont_MPair, CraneCont_MPair_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&m});
  /// Loopified sum_md: CraneEnter -> CraneCont_MPair -> CraneCont_MPair_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyMutualResultTypes::md &m = *_f.m;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::md::MNull>(
              m.v())) {
        _result = UINT64_C(0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualResultTypes::md::MConst>(m.v())) {
        const auto &[x0] =
            std::get<typename LoopifyMutualResultTypes::md::MConst>(m.v());
        const LoopifyMutualResultTypes::e &_inl_x = *x0;
        if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
                _inl_x.v())) {
          const auto &[_inl_n0] =
              std::get<typename LoopifyMutualResultTypes::e::Leaf>(_inl_x.v());
          _result = std::move(_inl_n0);
        } else if (std::holds_alternative<
                       typename LoopifyMutualResultTypes::e::Add>(_inl_x.v())) {
          const auto &[_inl_a0, _inl_b0] =
              std::get<typename LoopifyMutualResultTypes::e::Add>(_inl_x.v());
          _result = (sum_e(*_inl_a0) + sum_e(*_inl_b0));
        } else {
          const auto &[_inl_m0] =
              std::get<typename LoopifyMutualResultTypes::e::Meta>(_inl_x.v());
          _stack.emplace_back(CraneEnter{crane_raw(_inl_m0)});
        }
      } else {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::md::MPair>(m.v());
        _stack.emplace_back(CraneCont_MPair{crane_raw(b0)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_MPair>(_frame)) {
      auto _f = std::move(std::get<CraneCont_MPair>(_frame));
      const LoopifyMutualResultTypes::md &b0 = *_f.b0;
      _stack.emplace_back(CraneCont_MPair_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&b0});
    } else {
      auto _f = std::move(std::get<CraneCont_MPair_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

/// 2 * (1 + 2 + 3 + 4)
bool LoopifyMutualResultTypes::check(std::monostate) {
  return sum_e(dbl_e(sample)) == UINT64_C(20);
}
