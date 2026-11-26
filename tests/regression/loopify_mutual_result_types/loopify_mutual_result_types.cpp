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
LoopifyMutualResultTypes::dbl_e(const LoopifyMutualResultTypes::e &x) {
  // Explicit stack replaces the non-tail recursion of dbl_e: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMutualResultTypes::e *x;
  };

  struct _after_dbl_e_in_Add {
    const LoopifyMutualResultTypes::e *b0;
  };

  struct _after_dbl_e_in_Add_2 {
    LoopifyMutualResultTypes::e _tmp2;
  };

  struct _after_dbl_e_in_MConst {};

  using _frame = std::variant<_call, _after_dbl_e_in_Add, _after_dbl_e_in_Add_2,
                              _after_dbl_e_in_MConst>;
  LoopifyMutualResultTypes::e _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::e &x = *_f.x;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
              x.v())) {
        const auto &[n0] =
            std::get<typename LoopifyMutualResultTypes::e::Leaf>(x.v());
        _result = e::leaf((UINT64_C(2) * n0));
      } else if (
          std::holds_alternative<typename LoopifyMutualResultTypes::e::Add>(
              x.v())) {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::e::Add>(x.v());
        _stack.emplace_back(_after_dbl_e_in_Add{crane_raw(b0)});
        _stack.emplace_back(_call{crane_raw(a0)});
      } else {
        const auto &[m0] =
            std::get<typename LoopifyMutualResultTypes::e::Meta>(x.v());
        auto &&_sv0 = *m0;
        if (std::holds_alternative<typename LoopifyMutualResultTypes::md::MNull>(
                _sv0.v())) {
          _result = e::meta(md::mnull());
        } else if (std::holds_alternative<
                       typename LoopifyMutualResultTypes::md::MConst>(_sv0.v())) {
          const auto &[x1] =
              std::get<typename LoopifyMutualResultTypes::md::MConst>(_sv0.v());
          _stack.emplace_back(_after_dbl_e_in_MConst{});
          _stack.emplace_back(_call{crane_raw(x1)});
        } else {
          const auto &[a0, b0] =
              std::get<typename LoopifyMutualResultTypes::md::MPair>(_sv0.v());
          _result = e::meta(md::mpair(dbl_md(*a0), dbl_md(*b0)));
        }
      }
    } else if (std::holds_alternative<_after_dbl_e_in_Add>(_popped)) {
      auto _f = std::move(std::get<_after_dbl_e_in_Add>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::e &b0 = *_f.b0;
      _stack.emplace_back(_after_dbl_e_in_Add_2{std::move(_result)});
      _stack.emplace_back(_call{&b0});
    } else if (std::holds_alternative<_after_dbl_e_in_Add_2>(_popped)) {
      auto _f = std::move(std::get<_after_dbl_e_in_Add_2>(_popped));
      _stack.pop_back();
      _result = e::add(std::move(_f._tmp2), std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_dbl_e_in_MConst>(_popped));
      _stack.pop_back();
      _result = e::meta(md::mconst(std::move(_result)));
    }
  }
  return _result;
}

LoopifyMutualResultTypes::md
LoopifyMutualResultTypes::dbl_md(const LoopifyMutualResultTypes::md &m) {
  // Explicit stack replaces the non-tail recursion of dbl_md: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMutualResultTypes::md *m;
  };

  struct _after_dbl_md_in_MPair {
    const LoopifyMutualResultTypes::md *b0;
  };

  struct _after_dbl_md_in_MPair_2 {
    LoopifyMutualResultTypes::md _tmp8;
  };

  struct _after_dbl_md_in_Meta {};

  using _frame = std::variant<_call, _after_dbl_md_in_MPair,
                              _after_dbl_md_in_MPair_2, _after_dbl_md_in_Meta>;
  LoopifyMutualResultTypes::md _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&m});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::md &m = *_f.m;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::md::MNull>(
              m.v())) {
        _result = md::mnull();
      } else if (
          std::holds_alternative<typename LoopifyMutualResultTypes::md::MConst>(
              m.v())) {
        const auto &[x0] =
            std::get<typename LoopifyMutualResultTypes::md::MConst>(m.v());
        auto &&_sv0 = *x0;
        if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
                _sv0.v())) {
          const auto &[n0] =
              std::get<typename LoopifyMutualResultTypes::e::Leaf>(_sv0.v());
          _result = md::mconst(e::leaf((UINT64_C(2) * n0)));
        } else if (
            std::holds_alternative<typename LoopifyMutualResultTypes::e::Add>(
                _sv0.v())) {
          const auto &[a0, b0] =
              std::get<typename LoopifyMutualResultTypes::e::Add>(_sv0.v());
          _result = md::mconst(e::add(dbl_e(*a0), dbl_e(*b0)));
        } else {
          const auto &[m1] =
              std::get<typename LoopifyMutualResultTypes::e::Meta>(_sv0.v());
          _stack.emplace_back(_after_dbl_md_in_Meta{});
          _stack.emplace_back(_call{crane_raw(m1)});
        }
      } else {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::md::MPair>(m.v());
        _stack.emplace_back(_after_dbl_md_in_MPair{crane_raw(b0)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_dbl_md_in_MPair>(_popped)) {
      auto _f = std::move(std::get<_after_dbl_md_in_MPair>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::md &b0 = *_f.b0;
      _stack.emplace_back(_after_dbl_md_in_MPair_2{std::move(_result)});
      _stack.emplace_back(_call{&b0});
    } else if (std::holds_alternative<_after_dbl_md_in_MPair_2>(_popped)) {
      auto _f = std::move(std::get<_after_dbl_md_in_MPair_2>(_popped));
      _stack.pop_back();
      _result = md::mpair(std::move(_f._tmp8), std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_dbl_md_in_Meta>(_popped));
      _stack.pop_back();
      _result = md::mconst(e::meta(std::move(_result)));
    }
  }
  return _result;
}

uint64_t LoopifyMutualResultTypes::sum_e(const LoopifyMutualResultTypes::e &x) {
  // Explicit stack replaces the non-tail recursion of sum_e: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMutualResultTypes::e *x;
  };

  struct _call_sum_md_entry {
    const LoopifyMutualResultTypes::md *m;
  };

  struct _after_sum_e_in_Add {
    const LoopifyMutualResultTypes::e *b0;
  };

  struct _after_sum_e_in_Add_2 {
    uint64_t _tmp4;
  };

  struct _after_sum_md_entry_in_MPair {
    const LoopifyMutualResultTypes::md *b1;
  };

  struct _after_sum_md_entry_in_MPair_2 {
    uint64_t _tmp6;
  };

  struct _after_sum_md_entry_in_MPair_3 {
    const LoopifyMutualResultTypes::md *b0;
  };

  struct _after_sum_md_entry_in_MPair_4 {
    uint64_t _tmp2;
  };

  using _frame = std::variant<
      _call, _call_sum_md_entry, _after_sum_e_in_Add, _after_sum_e_in_Add_2,
      _after_sum_md_entry_in_MPair, _after_sum_md_entry_in_MPair_2,
      _after_sum_md_entry_in_MPair_3, _after_sum_md_entry_in_MPair_4>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::e &x = *_f.x;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
              x.v())) {
        const auto &[n0] =
            std::get<typename LoopifyMutualResultTypes::e::Leaf>(x.v());
        _result = std::move(n0);
      } else if (
          std::holds_alternative<typename LoopifyMutualResultTypes::e::Add>(
              x.v())) {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::e::Add>(x.v());
        _stack.emplace_back(_after_sum_e_in_Add{crane_raw(b0)});
        _stack.emplace_back(_call{crane_raw(a0)});
      } else {
        const auto &[m0] =
            std::get<typename LoopifyMutualResultTypes::e::Meta>(x.v());
        auto &&_sv1 = *m0;
        if (std::holds_alternative<typename LoopifyMutualResultTypes::md::MNull>(
                _sv1.v())) {
          _result = UINT64_C(0);
        } else if (std::holds_alternative<
                       typename LoopifyMutualResultTypes::md::MConst>(_sv1.v())) {
          const auto &[x1] =
              std::get<typename LoopifyMutualResultTypes::md::MConst>(_sv1.v());
          _stack.emplace_back(_call{crane_raw(x1)});
        } else {
          const auto &[a1, b1] =
              std::get<typename LoopifyMutualResultTypes::md::MPair>(_sv1.v());
          _stack.emplace_back(_after_sum_md_entry_in_MPair{crane_raw(b1)});
          _stack.emplace_back(_call_sum_md_entry{crane_raw(a1)});
        }
      }
    } else if (std::holds_alternative<_call_sum_md_entry>(_popped)) {
      auto _f = std::move(std::get<_call_sum_md_entry>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::md &m = *_f.m;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::md::MNull>(
              m.v())) {
        _result = UINT64_C(0);
      } else if (
          std::holds_alternative<typename LoopifyMutualResultTypes::md::MConst>(
              m.v())) {
        const auto &[x1] =
            std::get<typename LoopifyMutualResultTypes::md::MConst>(m.v());
        _stack.emplace_back(_call{crane_raw(x1)});
      } else {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::md::MPair>(m.v());
        _stack.emplace_back(_after_sum_md_entry_in_MPair_3{crane_raw(b0)});
        _stack.emplace_back(_call_sum_md_entry{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_sum_e_in_Add>(_popped)) {
      auto _f = std::move(std::get<_after_sum_e_in_Add>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::e &b0 = *_f.b0;
      _stack.emplace_back(_after_sum_e_in_Add_2{_result});
      _stack.emplace_back(_call{&b0});
    } else if (std::holds_alternative<_after_sum_e_in_Add_2>(_popped)) {
      auto _f = std::move(std::get<_after_sum_e_in_Add_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp4 + _result);
    } else if (std::holds_alternative<_after_sum_md_entry_in_MPair>(_popped)) {
      auto _f = std::move(std::get<_after_sum_md_entry_in_MPair>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::md &b1 = *_f.b1;
      _stack.emplace_back(_after_sum_md_entry_in_MPair_2{_result});
      _stack.emplace_back(_call_sum_md_entry{&b1});
    } else if (std::holds_alternative<_after_sum_md_entry_in_MPair_2>(_popped)) {
      auto _f = std::move(std::get<_after_sum_md_entry_in_MPair_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp6 + _result);
    } else if (std::holds_alternative<_after_sum_md_entry_in_MPair_3>(_popped)) {
      auto _f = std::move(std::get<_after_sum_md_entry_in_MPair_3>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::md &b0 = *_f.b0;
      _stack.emplace_back(_after_sum_md_entry_in_MPair_4{_result});
      _stack.emplace_back(_call_sum_md_entry{&b0});
    } else {
      auto _f = std::move(std::get<_after_sum_md_entry_in_MPair_4>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + _result);
    }
  }
  return _result;
}

uint64_t
LoopifyMutualResultTypes::sum_md(const LoopifyMutualResultTypes::md &m) {
  // Explicit stack replaces the non-tail recursion of sum_md: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyMutualResultTypes::md *m;
  };

  struct _call_sum_e_entry {
    const LoopifyMutualResultTypes::e *x;
  };

  struct _after_sum_e_entry_in_Add {
    const LoopifyMutualResultTypes::e *b1;
  };

  struct _after_sum_e_entry_in_Add_2 {
    uint64_t _tmp4;
  };

  struct _after_sum_e_entry_in_Add_3 {
    const LoopifyMutualResultTypes::e *b0;
  };

  struct _after_sum_e_entry_in_Add_4 {
    uint64_t _tmp2;
  };

  struct _after_sum_md_in_MPair {
    const LoopifyMutualResultTypes::md *b0;
  };

  struct _after_sum_md_in_MPair_2 {
    uint64_t _tmp6;
  };

  using _frame =
      std::variant<_call, _call_sum_e_entry, _after_sum_e_entry_in_Add,
                   _after_sum_e_entry_in_Add_2, _after_sum_e_entry_in_Add_3,
                   _after_sum_e_entry_in_Add_4, _after_sum_md_in_MPair,
                   _after_sum_md_in_MPair_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&m});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::md &m = *_f.m;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::md::MNull>(
              m.v())) {
        _result = UINT64_C(0);
      } else if (
          std::holds_alternative<typename LoopifyMutualResultTypes::md::MConst>(
              m.v())) {
        const auto &[x0] =
            std::get<typename LoopifyMutualResultTypes::md::MConst>(m.v());
        auto &&_sv1 = *x0;
        if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
                _sv1.v())) {
          const auto &[n1] =
              std::get<typename LoopifyMutualResultTypes::e::Leaf>(_sv1.v());
          _result = std::move(n1);
        } else if (
            std::holds_alternative<typename LoopifyMutualResultTypes::e::Add>(
                _sv1.v())) {
          const auto &[a1, b1] =
              std::get<typename LoopifyMutualResultTypes::e::Add>(_sv1.v());
          _stack.emplace_back(_after_sum_e_entry_in_Add{crane_raw(b1)});
          _stack.emplace_back(_call_sum_e_entry{crane_raw(a1)});
        } else {
          const auto &[m1] =
              std::get<typename LoopifyMutualResultTypes::e::Meta>(_sv1.v());
          _stack.emplace_back(_call{crane_raw(m1)});
        }
      } else {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::md::MPair>(m.v());
        _stack.emplace_back(_after_sum_md_in_MPair{crane_raw(b0)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_call_sum_e_entry>(_popped)) {
      auto _f = std::move(std::get<_call_sum_e_entry>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::e &x = *_f.x;
      if (std::holds_alternative<typename LoopifyMutualResultTypes::e::Leaf>(
              x.v())) {
        const auto &[n0] =
            std::get<typename LoopifyMutualResultTypes::e::Leaf>(x.v());
        _result = std::move(n0);
      } else if (
          std::holds_alternative<typename LoopifyMutualResultTypes::e::Add>(
              x.v())) {
        const auto &[a0, b0] =
            std::get<typename LoopifyMutualResultTypes::e::Add>(x.v());
        _stack.emplace_back(_after_sum_e_entry_in_Add_3{crane_raw(b0)});
        _stack.emplace_back(_call_sum_e_entry{crane_raw(a0)});
      } else {
        const auto &[m1] =
            std::get<typename LoopifyMutualResultTypes::e::Meta>(x.v());
        _stack.emplace_back(_call{crane_raw(m1)});
      }
    } else if (std::holds_alternative<_after_sum_e_entry_in_Add>(_popped)) {
      auto _f = std::move(std::get<_after_sum_e_entry_in_Add>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::e &b1 = *_f.b1;
      _stack.emplace_back(_after_sum_e_entry_in_Add_2{_result});
      _stack.emplace_back(_call_sum_e_entry{&b1});
    } else if (std::holds_alternative<_after_sum_e_entry_in_Add_2>(_popped)) {
      auto _f = std::move(std::get<_after_sum_e_entry_in_Add_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp4 + _result);
    } else if (std::holds_alternative<_after_sum_e_entry_in_Add_3>(_popped)) {
      auto _f = std::move(std::get<_after_sum_e_entry_in_Add_3>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::e &b0 = *_f.b0;
      _stack.emplace_back(_after_sum_e_entry_in_Add_4{_result});
      _stack.emplace_back(_call_sum_e_entry{&b0});
    } else if (std::holds_alternative<_after_sum_e_entry_in_Add_4>(_popped)) {
      auto _f = std::move(std::get<_after_sum_e_entry_in_Add_4>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + _result);
    } else if (std::holds_alternative<_after_sum_md_in_MPair>(_popped)) {
      auto _f = std::move(std::get<_after_sum_md_in_MPair>(_popped));
      _stack.pop_back();
      const LoopifyMutualResultTypes::md &b0 = *_f.b0;
      _stack.emplace_back(_after_sum_md_in_MPair_2{_result});
      _stack.emplace_back(_call{&b0});
    } else {
      auto _f = std::move(std::get<_after_sum_md_in_MPair_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp6 + _result);
    }
  }
  return _result;
}

/// 2 * (1 + 2 + 3 + 4)
bool LoopifyMutualResultTypes::check() {
  return sum_e(dbl_e(sample)) == UINT64_C(20);
}
