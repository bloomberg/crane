#include "reuse_forced_views.h"

ReuseForcedViews::tree ReuseForcedViews::smash(ReuseForcedViews::tree t,
                                               ReuseForcedViews::tree u) {
  if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
          t.v_mut())) {
    return tree::leaf();
  } else {
    auto &[a0, a1, a2] =
        std::get<typename ReuseForcedViews::tree::Node>(t.v_mut());
    auto &&_sv = *a2;
    if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
            _sv.v())) {
      if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
              u.v_mut())) {
        return tree::leaf();
      } else {
        auto &[a01, a11, a21] =
            std::get<typename ReuseForcedViews::tree::Node>(u.v_mut());
        auto &&_sv = *a21;
        if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                _sv.v())) {
          if (a01 < a0) {
            return tree::node(
                std::move(a0),
                tree::node(std::move(a01), crane::child(a11), crane::child(a1)),
                tree::leaf());
          } else {
            return tree::node(
                std::move(a01),
                tree::node(std::move(a0), crane::child(a1), crane::child(a11)),
                tree::leaf());
          }
        } else {
          return tree::leaf();
        }
      }
    } else {
      return tree::leaf();
    }
  }
}

List<ReuseForcedViews::tree>
ReuseForcedViews::carry(List<ReuseForcedViews::tree> q,
                        ReuseForcedViews::tree t) {
  crane::rc<List<ReuseForcedViews::tree>> _head{};
  crane::rc<List<ReuseForcedViews::tree>> *_write = &_head;
  crane::rc<List<ReuseForcedViews::tree>> _own =
      crane::rc<List<ReuseForcedViews::tree>>();
  bool _uniq = true;
  ReuseForcedViews::tree _loop_t = std::move(t);
  const List<ReuseForcedViews::tree> *_loop_q = &q;
  while (true) {
    if (std::holds_alternative<typename List<ReuseForcedViews::tree>::Nil>(
            _loop_q->v())) {
      if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
              _loop_t.v_mut())) {
        *_write = crane::make_rc<List<ReuseForcedViews::tree>>(
            List<ReuseForcedViews::tree>::nil());
        break;
      } else {
        *_write = crane::make_rc<List<ReuseForcedViews::tree>>(
            List<ReuseForcedViews::tree>::cons(
                _loop_t, List<ReuseForcedViews::tree>::nil()));
        break;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<ReuseForcedViews::tree>::Cons>(_loop_q->v());
      if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
              a0.v())) {
        *_write = crane::make_rc<List<ReuseForcedViews::tree>>(
            List<ReuseForcedViews::tree>::cons(std::move(_loop_t),
                                               crane::child(a1)));
        break;
      } else {
        if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                _loop_t.v_mut())) {
          *_write = crane::make_rc<List<ReuseForcedViews::tree>>(
              List<ReuseForcedViews::tree>::cons(a0, crane::child(a1)));
          break;
        } else {
          auto _read = smash(_loop_t, a0);
          auto _rs = crane::reuse_step(_own, _uniq, a1);
          auto _cell = crane::make_rc_reusing_unchecked(
              std::move(_rs.token), typename List<ReuseForcedViews::tree>::Cons(
                                        tree::leaf(), nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<ReuseForcedViews::tree>::Cons>(
                        (*_write)->v_mut())
                        .l;
          _loop_t = std::move(_read);
          _own = std::move(_rs.next);
          _loop_q = _own.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<std::pair<uint64_t,
               std::pair<std::optional<uint64_t>, std::optional<uint64_t>>>>
ReuseForcedViews::combine(List<std::pair<uint64_t, uint64_t>> m,
                          const List<std::pair<uint64_t, uint64_t>>
                              &x0_) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const List<std::pair<uint64_t, uint64_t>> *x0_;
    const List<std::pair<uint64_t, uint64_t>> *m;
  };

  /// CraneEnter_combine_aux: captures varying parameters for each recursive
  /// call.
  struct CraneEnter_combine_aux {
    const List<std::pair<uint64_t, uint64_t>> *m_;
    const List<std::pair<uint64_t, uint64_t>> *a1_value;
    uint64_t e;
    uint64_t k;
    List<std::pair<uint64_t, uint64_t>> m;
  };

  /// CraneCont1: saves [k, e], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t k;
    uint64_t e;
  };

  /// CraneCont2: saves [k, e, e_], resumes after recursive call, then processes
  /// rest.
  struct CraneCont2 {
    uint64_t k;
    uint64_t e;
    uint64_t e_;
  };

  /// CraneCont3: saves [k_, e_], resumes after recursive call, then processes
  /// rest.
  struct CraneCont3 {
    uint64_t k_;
    uint64_t e_;
  };

  using CraneFrame = std::variant<CraneEnter, CraneEnter_combine_aux,
                                  CraneCont1, CraneCont2, CraneCont3>;
  List<std::pair<uint64_t,
                 std::pair<std::optional<uint64_t>, std::optional<uint64_t>>>>
      _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&x0_, &m});
  /// Loopified combine: CraneEnter -> CraneCont1 -> CraneCont2 -> CraneCont3.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &x0_ = *_f.x0_;
      const List<std::pair<uint64_t, uint64_t>> &m = *_f.m;
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(m.v())) {
        _result = x0_.template map<
            std::pair<uint64_t, std::pair<std::optional<uint64_t>,
                                          std::optional<uint64_t>>>>(
            [](const std::pair<uint64_t, uint64_t> &p) {
              return std::make_pair(
                  p.first,
                  std::make_pair(std::optional<uint64_t>(),
                                 std::make_optional<uint64_t>(p.second)));
            });
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(m.v());
        const List<std::pair<uint64_t, uint64_t>> &a1_value = *a1;
        const auto &[k, e] = a0;
        _stack.emplace_back(
            CraneEnter_combine_aux{&x0_, crane_raw(a1), e, k, m});
      }
    } else if (std::holds_alternative<CraneEnter_combine_aux>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_combine_aux>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &m_ = *_f.m_;
      const List<std::pair<uint64_t, uint64_t>> &a1_value = *_f.a1_value;
      uint64_t e = _f.e;
      uint64_t k = _f.k;
      List<std::pair<uint64_t, uint64_t>> m = std::move(_f.m);
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(m_.v())) {
        _result = m.template map<
            std::pair<uint64_t, std::pair<std::optional<uint64_t>,
                                          std::optional<uint64_t>>>>(
            [](const std::pair<uint64_t, uint64_t> &p0) {
              return std::make_pair(
                  p0.first,
                  std::make_pair(std::make_optional<uint64_t>(p0.second),
                                 std::optional<uint64_t>()));
            });
      } else {
        const auto &[a00, a10] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                m_.v());
        const auto &[k_, e_] = a00;
        if (k < k_) {
          _stack.emplace_back(CraneCont1{k, e});
          _stack.emplace_back(CraneEnter{&m_, &a1_value});
        } else {
          if (k == k_) {
            _stack.emplace_back(CraneCont2{k, e, e_});
            _stack.emplace_back(CraneEnter{crane_raw(a10), &a1_value});
          } else {
            _stack.emplace_back(CraneCont3{k_, e_});
            _stack.emplace_back(
                CraneEnter_combine_aux{crane_raw(a10), &a1_value, e, k, m});
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t k = _f.k;
      uint64_t e = _f.e;
      _result = List<std::pair<uint64_t, std::pair<std::optional<uint64_t>,
                                                   std::optional<uint64_t>>>>::
          cons(std::make_pair(k, std::make_pair(std::make_optional<uint64_t>(e),
                                                std::optional<uint64_t>())),
               std::move(_result));
    } else if (std::holds_alternative<CraneCont2>(_frame)) {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      uint64_t k = _f.k;
      uint64_t e = _f.e;
      uint64_t e_ = _f.e_;
      _result = List<std::pair<uint64_t, std::pair<std::optional<uint64_t>,
                                                   std::optional<uint64_t>>>>::
          cons(std::make_pair(k,
                              std::make_pair(std::make_optional<uint64_t>(e),
                                             std::make_optional<uint64_t>(e_))),
               std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont3>(_frame));
      uint64_t k_ = _f.k_;
      uint64_t e_ = _f.e_;
      _result = List<std::pair<uint64_t, std::pair<std::optional<uint64_t>,
                                                   std::optional<uint64_t>>>>::
          cons(std::make_pair(k_,
                              std::make_pair(std::optional<uint64_t>(),
                                             std::make_optional<uint64_t>(e_))),
               std::move(_result));
    }
  }
  return _result;
}
