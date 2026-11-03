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

  /// CraneCont_MConst: resumes after recursive call, then processes rest.
  struct CraneCont_MConst {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                                  CraneCont_MConst>;
  LoopifyMutualResultTypes::e _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&x});
  /// Loopified dbl_e: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
  /// CraneCont_MConst.
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
        auto &&_sv0 = *m0;
        if (std::holds_alternative<
                typename LoopifyMutualResultTypes::md::MNull>(_sv0.v())) {
          _result = e::meta(md::mnull());
        } else if (std::holds_alternative<
                       typename LoopifyMutualResultTypes::md::MConst>(
                       _sv0.v())) {
          const auto &[x1] =
              std::get<typename LoopifyMutualResultTypes::md::MConst>(_sv0.v());
          _stack.emplace_back(CraneCont_MConst{});
          _stack.emplace_back(CraneEnter{crane_raw(x1)});
        } else {
          const auto &[a0, b0] =
              std::get<typename LoopifyMutualResultTypes::md::MPair>(_sv0.v());
          _result = e::meta(md::mpair(dbl_md(*a0), dbl_md(*b0)));
        }
      }
    } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Add>(_frame));
      const LoopifyMutualResultTypes::e &b0 = *_f.b0;
      _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&b0});
    } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
      _result = e::add(std::move(_f._tmp2), std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont_MConst>(_frame));
      _result = e::meta(md::mconst(std::move(_result)));
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

  /// CraneCont_MPair_1: saves [_tmp8], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_MPair_1 {
    LoopifyMutualResultTypes::md _tmp8;
  };

  /// CraneCont_Meta: resumes after recursive call, then processes rest.
  struct CraneCont_Meta {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_MPair,
                                  CraneCont_MPair_1, CraneCont_Meta>;
  LoopifyMutualResultTypes::md _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&m});
  /// Loopified dbl_md: CraneEnter -> CraneCont_MPair -> CraneCont_MPair_1 ->
  /// CraneCont_Meta.
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
        auto &&_sv0 = *x0;
        if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
                _sv0.v())) {
          const auto &[n0] =
              std::get<typename LoopifyMutualResultTypes::e::Leaf>(_sv0.v());
          _result = md::mconst(e::leaf((UINT64_C(2) * n0)));
        } else if (std::holds_alternative<
                       typename LoopifyMutualResultTypes::e::Add>(_sv0.v())) {
          const auto &[a0, b0] =
              std::get<typename LoopifyMutualResultTypes::e::Add>(_sv0.v());
          _result = md::mconst(e::add(dbl_e(*a0), dbl_e(*b0)));
        } else {
          const auto &[m1] =
              std::get<typename LoopifyMutualResultTypes::e::Meta>(_sv0.v());
          _stack.emplace_back(CraneCont_Meta{});
          _stack.emplace_back(CraneEnter{crane_raw(m1)});
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
    } else if (std::holds_alternative<CraneCont_MPair_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_MPair_1>(_frame));
      _result = md::mpair(std::move(_f._tmp8), std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont_Meta>(_frame));
      _result = md::mconst(e::meta(std::move(_result)));
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

  /// CraneEnter_sum_md_entry: captures varying parameters for each recursive
  /// call.
  struct CraneEnter_sum_md_entry {
    const LoopifyMutualResultTypes::md *m;
  };

  /// CraneCont_Add: saves [b0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Add {
    const LoopifyMutualResultTypes::e *b0;
  };

  /// CraneCont_Add_1: saves [_tmp4], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Add_1 {
    uint64_t _tmp4;
  };

  /// CraneCont_MPair: saves [b1], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_MPair {
    const LoopifyMutualResultTypes::md *b1;
  };

  /// CraneCont_MPair_1: saves [_tmp6], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_MPair_1 {
    uint64_t _tmp6;
  };

  /// CraneCont_MPair_2: saves [b0], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_MPair_2 {
    const LoopifyMutualResultTypes::md *b0;
  };

  /// CraneCont_MPair_3: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_MPair_3 {
    uint64_t _tmp2;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneEnter_sum_md_entry, CraneCont_Add,
                   CraneCont_Add_1, CraneCont_MPair, CraneCont_MPair_1,
                   CraneCont_MPair_2, CraneCont_MPair_3>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&x});
  /// Loopified sum_e: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
  /// CraneCont_MPair -> CraneCont_MPair_1 -> CraneCont_MPair_2 ->
  /// CraneCont_MPair_3.
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
        auto &&_sv1 = *m0;
        if (std::holds_alternative<
                typename LoopifyMutualResultTypes::md::MNull>(_sv1.v())) {
          _result = UINT64_C(0);
        } else if (std::holds_alternative<
                       typename LoopifyMutualResultTypes::md::MConst>(
                       _sv1.v())) {
          const auto &[x1] =
              std::get<typename LoopifyMutualResultTypes::md::MConst>(_sv1.v());
          _stack.emplace_back(CraneEnter{crane_raw(x1)});
        } else {
          const auto &[a1, b1] =
              std::get<typename LoopifyMutualResultTypes::md::MPair>(_sv1.v());
          _stack.emplace_back(CraneCont_MPair{crane_raw(b1)});
          _stack.emplace_back(CraneEnter_sum_md_entry{crane_raw(a1)});
        }
      }
    } else if (std::holds_alternative<CraneEnter_sum_md_entry>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_sum_md_entry>(_frame));
      const LoopifyMutualResultTypes::md &m = *_f.m;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::md::MNull>(
              m.v())) {
        _result = UINT64_C(0);
      } else if (std::holds_alternative<
                     typename LoopifyMutualResultTypes::md::MConst>(m.v())) {
        const auto &[x1] =
            std::get<typename LoopifyMutualResultTypes::md::MConst>(m.v());
        _stack.emplace_back(CraneEnter{crane_raw(x1)});
      } else {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::md::MPair>(m.v());
        _stack.emplace_back(CraneCont_MPair_2{crane_raw(b0)});
        _stack.emplace_back(CraneEnter_sum_md_entry{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Add>(_frame));
      const LoopifyMutualResultTypes::e &b0 = *_f.b0;
      _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&b0});
    } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
      _result = (_f._tmp4 + std::move(_result));
    } else if (std::holds_alternative<CraneCont_MPair>(_frame)) {
      auto _f = std::move(std::get<CraneCont_MPair>(_frame));
      const LoopifyMutualResultTypes::md &b1 = *_f.b1;
      _stack.emplace_back(CraneCont_MPair_1{std::move(_result)});
      _stack.emplace_back(CraneEnter_sum_md_entry{&b1});
    } else if (std::holds_alternative<CraneCont_MPair_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_MPair_1>(_frame));
      _result = (_f._tmp6 + std::move(_result));
    } else if (std::holds_alternative<CraneCont_MPair_2>(_frame)) {
      auto _f = std::move(std::get<CraneCont_MPair_2>(_frame));
      const LoopifyMutualResultTypes::md &b0 = *_f.b0;
      _stack.emplace_back(CraneCont_MPair_3{std::move(_result)});
      _stack.emplace_back(CraneEnter_sum_md_entry{&b0});
    } else {
      auto _f = std::move(std::get<CraneCont_MPair_3>(_frame));
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

  /// CraneEnter_sum_e_entry: captures varying parameters for each recursive
  /// call.
  struct CraneEnter_sum_e_entry {
    const LoopifyMutualResultTypes::e *x;
  };

  /// CraneCont_Add: saves [b1], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Add {
    const LoopifyMutualResultTypes::e *b1;
  };

  /// CraneCont_Add_1: saves [_tmp4], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Add_1 {
    uint64_t _tmp4;
  };

  /// CraneCont_Add_2: saves [b0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Add_2 {
    const LoopifyMutualResultTypes::e *b0;
  };

  /// CraneCont_Add_3: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Add_3 {
    uint64_t _tmp2;
  };

  /// CraneCont_MPair: saves [b0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_MPair {
    const LoopifyMutualResultTypes::md *b0;
  };

  /// CraneCont_MPair_1: saves [_tmp6], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_MPair_1 {
    uint64_t _tmp6;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneEnter_sum_e_entry, CraneCont_Add,
                   CraneCont_Add_1, CraneCont_Add_2, CraneCont_Add_3,
                   CraneCont_MPair, CraneCont_MPair_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&m});
  /// Loopified sum_md: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
  /// CraneCont_Add_2 -> CraneCont_Add_3 -> CraneCont_MPair ->
  /// CraneCont_MPair_1.
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
        auto &&_sv1 = *x0;
        if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
                _sv1.v())) {
          const auto &[n1] =
              std::get<typename LoopifyMutualResultTypes::e::Leaf>(_sv1.v());
          _result = std::move(n1);
        } else if (std::holds_alternative<
                       typename LoopifyMutualResultTypes::e::Add>(_sv1.v())) {
          const auto &[a1, b1] =
              std::get<typename LoopifyMutualResultTypes::e::Add>(_sv1.v());
          _stack.emplace_back(CraneCont_Add{crane_raw(b1)});
          _stack.emplace_back(CraneEnter_sum_e_entry{crane_raw(a1)});
        } else {
          const auto &[m1] =
              std::get<typename LoopifyMutualResultTypes::e::Meta>(_sv1.v());
          _stack.emplace_back(CraneEnter{crane_raw(m1)});
        }
      } else {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::md::MPair>(m.v());
        _stack.emplace_back(CraneCont_MPair{crane_raw(b0)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneEnter_sum_e_entry>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_sum_e_entry>(_frame));
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
        _stack.emplace_back(CraneCont_Add_2{crane_raw(b0)});
        _stack.emplace_back(CraneEnter_sum_e_entry{crane_raw(a0)});
      } else {
        const auto &[m1] =
            std::get<typename LoopifyMutualResultTypes::e::Meta>(x.v());
        _stack.emplace_back(CraneEnter{crane_raw(m1)});
      }
    } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Add>(_frame));
      const LoopifyMutualResultTypes::e &b1 = *_f.b1;
      _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
      _stack.emplace_back(CraneEnter_sum_e_entry{&b1});
    } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
      _result = (_f._tmp4 + std::move(_result));
    } else if (std::holds_alternative<CraneCont_Add_2>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Add_2>(_frame));
      const LoopifyMutualResultTypes::e &b0 = *_f.b0;
      _stack.emplace_back(CraneCont_Add_3{std::move(_result)});
      _stack.emplace_back(CraneEnter_sum_e_entry{&b0});
    } else if (std::holds_alternative<CraneCont_Add_3>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Add_3>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    } else if (std::holds_alternative<CraneCont_MPair>(_frame)) {
      auto _f = std::move(std::get<CraneCont_MPair>(_frame));
      const LoopifyMutualResultTypes::md &b0 = *_f.b0;
      _stack.emplace_back(CraneCont_MPair_1{std::move(_result)});
      _stack.emplace_back(CraneEnter{&b0});
    } else {
      auto _f = std::move(std::get<CraneCont_MPair_1>(_frame));
      _result = (_f._tmp6 + std::move(_result));
    }
  }
  return _result;
}

/// 2 * (1 + 2 + 3 + 4)
bool LoopifyMutualResultTypes::check(std::monostate) {
  return sum_e(dbl_e(sample)) == UINT64_C(20);
}
