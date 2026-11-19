#include "reuse_forced_views.h"

ReuseForcedViews::tree ReuseForcedViews::smash(ReuseForcedViews::tree t,
                                               ReuseForcedViews::tree u) {
  // Reuse the matched cell in place when this is its only owner; otherwise
  // rebuild.
  if (t.v().index() == 1) {
    if (std::get<typename ReuseForcedViews::tree::Node>(t.v_mut()).a1.use_count() ==
        1) {
      uint64_t x = std::move(
          std::get<typename ReuseForcedViews::tree::Node>(t.v_mut()).a0);
      ReuseForcedViews::tree t1 = std::move(
          *std::get<typename ReuseForcedViews::tree::Node>(t.v_mut()).a1);
      ReuseForcedViews::tree t0 =
          *std::get<typename ReuseForcedViews::tree::Node>(t.v_mut()).a2;
      if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
              t0.v_mut())) {
        // Reuse the matched cell in place when this is its only owner;
        // otherwise rebuild.
        if (u.v().index() == 1) {
          if (std::get<typename ReuseForcedViews::tree::Node>(u.v_mut()).a1.use_count() ==
              1) {
            uint64_t y = std::move(
                std::get<typename ReuseForcedViews::tree::Node>(u.v_mut()).a0);
            ReuseForcedViews::tree u1 = std::move(
                *std::get<typename ReuseForcedViews::tree::Node>(u.v_mut()).a1);
            ReuseForcedViews::tree t2 =
                *std::get<typename ReuseForcedViews::tree::Node>(u.v_mut()).a2;
            if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                    t2.v_mut())) {
              if (y < x) {
                return tree::node_crane_reuse(
                    std::move(std::get<typename ReuseForcedViews::tree::Node>(
                        u.v_mut())
                                  .a1),
                    std::move(x),
                    tree::node(std::move(y), std::move(u1), std::move(t1)),
                    tree::leaf());
              } else {
                return tree::node_crane_reuse(
                    std::move(std::get<typename ReuseForcedViews::tree::Node>(
                        u.v_mut())
                                  .a1),
                    std::move(y),
                    tree::node(std::move(x), std::move(t1), std::move(u1)),
                    tree::leaf());
              }
            } else {
              return tree::leaf();
            }
          } else {
            if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                    u.v_mut())) {
              return tree::leaf();
            } else {
              auto &[a01, a11, a21] =
                  std::get<typename ReuseForcedViews::tree::Node>(u.v_mut());
              auto &&_sv = *a21;
              if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                      _sv.v())) {
                if (a01 < x) {
                  return tree::node_crane_reuse(
                      std::move(std::get<typename ReuseForcedViews::tree::Node>(
                          t.v_mut())
                                    .a1),
                      std::move(x),
                      tree::node(std::move(a01), crane::child(a11),
                                 std::move(t1)),
                      tree::leaf());
                } else {
                  return tree::node_crane_reuse(
                      std::move(std::get<typename ReuseForcedViews::tree::Node>(
                          t.v_mut())
                                    .a1),
                      std::move(a01), tree::node(std::move(x), std::move(t1),
                                                 crane::child(a11)),
                      tree::leaf());
                }
              } else {
                return tree::leaf();
              }
            }
          }
        } else {
          if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                  u.v_mut())) {
            return tree::leaf();
          } else {
            auto &[a01, a11, a21] =
                std::get<typename ReuseForcedViews::tree::Node>(u.v_mut());
            auto &&_sv = *a21;
            if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                    _sv.v())) {
              if (a01 < x) {
                return tree::node_crane_reuse(
                    std::move(std::get<typename ReuseForcedViews::tree::Node>(
                        t.v_mut())
                                  .a1),
                    std::move(x), tree::node(std::move(a01), crane::child(a11),
                                             std::move(t1)),
                    tree::leaf());
              } else {
                return tree::node_crane_reuse(
                    std::move(std::get<typename ReuseForcedViews::tree::Node>(
                        t.v_mut())
                                  .a1),
                    std::move(a01),
                    tree::node(std::move(x), std::move(t1), crane::child(a11)),
                    tree::leaf());
              }
            } else {
              return tree::leaf();
            }
          }
        }
      } else {
        return tree::leaf();
      }
    } else {
      if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
              t.v_mut())) {
        return tree::leaf();
      } else {
        auto &[a0, a1, a2] =
            std::get<typename ReuseForcedViews::tree::Node>(t.v_mut());
        auto &&_sv = *a2;
        if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                _sv.v())) {
          // Reuse the matched cell in place when this is its only owner;
          // otherwise rebuild.
          if (u.v().index() == 1) {
            if (std::get<typename ReuseForcedViews::tree::Node>(u.v_mut()).a1.use_count() ==
                1) {
              uint64_t y =
                  std::move(std::get<typename ReuseForcedViews::tree::Node>(
                      u.v_mut())
                                .a0);
              ReuseForcedViews::tree u1 =
                  std::move(*std::get<typename ReuseForcedViews::tree::Node>(
                      u.v_mut())
                                .a1);
              ReuseForcedViews::tree t2 =
                  *std::get<typename ReuseForcedViews::tree::Node>(u.v_mut()).a2;
              if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                      t2.v_mut())) {
                if (y < a0) {
                  return tree::node_crane_reuse(
                      std::move(std::get<typename ReuseForcedViews::tree::Node>(
                          u.v_mut())
                                    .a1),
                      std::move(a0),
                      tree::node(std::move(y), std::move(u1), crane::child(a1)),
                      tree::leaf());
                } else {
                  return tree::node_crane_reuse(
                      std::move(std::get<typename ReuseForcedViews::tree::Node>(
                          u.v_mut())
                                    .a1),
                      std::move(y), tree::node(std::move(a0), crane::child(a1),
                                               std::move(u1)),
                      tree::leaf());
                }
              } else {
                return tree::leaf();
              }
            } else {
              if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                      u.v_mut())) {
                return tree::leaf();
              } else {
                auto &[a01, a11, a21] =
                    std::get<typename ReuseForcedViews::tree::Node>(u.v_mut());
                auto &&_sv = *a21;
                if (std::holds_alternative<
                        typename ReuseForcedViews::tree::Leaf>(_sv.v())) {
                  if (a01 < a0) {
                    return tree::node(
                        std::move(a0),
                        tree::node(std::move(a01), crane::child(a11),
                                   crane::child(a1)),
                        tree::leaf());
                  } else {
                    return tree::node(
                        std::move(a01),
                        tree::node(std::move(a0), crane::child(a1),
                                   crane::child(a11)),
                        tree::leaf());
                  }
                } else {
                  return tree::leaf();
                }
              }
            }
          } else {
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
                  return tree::node(std::move(a0), tree::node(std::move(a01),
                                                              crane::child(a11),
                                                              crane::child(a1)),
                                    tree::leaf());
                } else {
                  return tree::node(std::move(a01),
                                    tree::node(std::move(a0), crane::child(a1),
                                               crane::child(a11)),
                                    tree::leaf());
                }
              } else {
                return tree::leaf();
              }
            }
          }
        } else {
          return tree::leaf();
        }
      }
    }
  } else {
    if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(t.v_mut())) {
      return tree::leaf();
    } else {
      auto &[a0, a1, a2] =
          std::get<typename ReuseForcedViews::tree::Node>(t.v_mut());
      auto &&_sv = *a2;
      if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(_sv.v())) {
        // Reuse the matched cell in place when this is its only owner;
        // otherwise rebuild.
        if (u.v().index() == 1) {
          if (std::get<typename ReuseForcedViews::tree::Node>(u.v_mut()).a1.use_count() ==
              1) {
            uint64_t y = std::move(
                std::get<typename ReuseForcedViews::tree::Node>(u.v_mut()).a0);
            ReuseForcedViews::tree u1 = std::move(
                *std::get<typename ReuseForcedViews::tree::Node>(u.v_mut()).a1);
            ReuseForcedViews::tree t2 =
                *std::get<typename ReuseForcedViews::tree::Node>(u.v_mut()).a2;
            if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                    t2.v_mut())) {
              if (y < a0) {
                return tree::node_crane_reuse(
                    std::move(std::get<typename ReuseForcedViews::tree::Node>(
                        u.v_mut())
                                  .a1),
                    std::move(a0),
                    tree::node(std::move(y), std::move(u1), crane::child(a1)),
                    tree::leaf());
              } else {
                return tree::node_crane_reuse(
                    std::move(std::get<typename ReuseForcedViews::tree::Node>(
                        u.v_mut())
                                  .a1),
                    std::move(y),
                    tree::node(std::move(a0), crane::child(a1), std::move(u1)),
                    tree::leaf());
              }
            } else {
              return tree::leaf();
            }
          } else {
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
                  return tree::node(std::move(a0), tree::node(std::move(a01),
                                                              crane::child(a11),
                                                              crane::child(a1)),
                                    tree::leaf());
                } else {
                  return tree::node(std::move(a01),
                                    tree::node(std::move(a0), crane::child(a1),
                                               crane::child(a11)),
                                    tree::leaf());
                }
              } else {
                return tree::leaf();
              }
            }
          }
        } else {
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
                return tree::node(std::move(a0),
                                  tree::node(std::move(a01), crane::child(a11),
                                             crane::child(a1)),
                                  tree::leaf());
              } else {
                return tree::node(std::move(a01),
                                  tree::node(std::move(a0), crane::child(a1),
                                             crane::child(a11)),
                                  tree::leaf());
              }
            } else {
              return tree::leaf();
            }
          }
        }
      } else {
        return tree::leaf();
      }
    }
  }
}

List<ReuseForcedViews::tree>
ReuseForcedViews::carry(List<ReuseForcedViews::tree> q,
                        ReuseForcedViews::tree t) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills. The input's cells are reused in place while uniquely owned.
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
              _loop_t.v())) {
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
      if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(a0.v())) {
        *_write = crane::make_rc<List<ReuseForcedViews::tree>>(
            List<ReuseForcedViews::tree>::cons(std::move(_loop_t),
                                               crane::child(a1)));
        break;
      } else {
        if (std::holds_alternative<typename ReuseForcedViews::tree::Leaf>(
                _loop_t.v())) {
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
          _write =
              &std::get<typename List<ReuseForcedViews::tree>::Cons>(
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
                          const List<std::pair<uint64_t, uint64_t>> &x0_) {
  // Explicit stack replaces the non-tail recursion of combine: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<std::pair<uint64_t, uint64_t>> *x0_;
    const List<std::pair<uint64_t, uint64_t>> *m;
  };

  struct _call_combine_aux {
    const List<std::pair<uint64_t, uint64_t>> *m_;
    const List<std::pair<uint64_t, uint64_t>> *a1_value;
    uint64_t e;
    uint64_t k;
    List<std::pair<uint64_t, uint64_t>> m;
  };

  struct _after_combine_aux_in_false {
    uint64_t k_;
    uint64_t e_;
  };

  struct _after_combine_in_true {
    uint64_t k;
    uint64_t e;
  };

  struct _after_combine_in_true_2 {
    uint64_t k;
    uint64_t e;
    uint64_t e_;
  };

  using _frame =
      std::variant<_call, _call_combine_aux, _after_combine_aux_in_false,
                   _after_combine_in_true, _after_combine_in_true_2>;
  List<std::pair<uint64_t,
                 std::pair<std::optional<uint64_t>,
                           std::optional<uint64_t>>>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x0_, &m});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<std::pair<uint64_t, uint64_t>> &x0_ = *_f.x0_;
      const List<std::pair<uint64_t, uint64_t>> &m = *_f.m;
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(m.v())) {
        _result = x0_.template map<
            std::pair<uint64_t, std::pair<std::optional<uint64_t>,
                                          std::optional<uint64_t>>>>([](
            const std::pair<uint64_t,
                            uint64_t> &p) {
          return std::make_pair(
              p.first, std::make_pair(std::optional<uint64_t>(),
                                      std::make_optional<uint64_t>(p.second)));
        });
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(m.v());
        const List<std::pair<uint64_t, uint64_t>> &a1_value = *a1;
        const auto &[k, e] = a0;
        _stack.emplace_back(_call_combine_aux{&x0_, crane_raw(a1), e, k, m});
      }
    } else if (std::holds_alternative<_call_combine_aux>(_popped)) {
      auto _f = std::move(std::get<_call_combine_aux>(_popped));
      _stack.pop_back();
      const List<std::pair<uint64_t, uint64_t>> &m_ = *_f.m_;
      const List<std::pair<uint64_t, uint64_t>> &a1_value = *_f.a1_value;
      uint64_t e = _f.e;
      uint64_t k = _f.k;
      List<std::pair<uint64_t, uint64_t>> m = std::move(_f.m);
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(m_.v())) {
        _result = m.template map<
            std::pair<uint64_t, std::pair<std::optional<uint64_t>,
                                          std::optional<uint64_t>>>>([](
            const std::pair<uint64_t,
                            uint64_t> &p0) {
          return std::make_pair(
              p0.first, std::make_pair(std::make_optional<uint64_t>(p0.second),
                                       std::optional<uint64_t>()));
        });
      } else {
        const auto &[a00, a10] = std::get<
            typename List<std::pair<uint64_t, uint64_t>>::Cons>(m_.v());
        const auto &[k_, e_] = a00;
        if (k < k_) {
          _stack.emplace_back(_after_combine_in_true{k, e});
          _stack.emplace_back(_call{&m_, &a1_value});
        } else {
          if (k == k_) {
            _stack.emplace_back(_after_combine_in_true_2{k, e, e_});
            _stack.emplace_back(_call{crane_raw(a10), &a1_value});
          } else {
            _stack.emplace_back(_after_combine_aux_in_false{k_, e_});
            _stack.emplace_back(_call_combine_aux{crane_raw(a10), &a1_value, e,
                                                  k, std::move(m)});
          }
        }
      }
    } else if (std::holds_alternative<_after_combine_aux_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_combine_aux_in_false>(_popped));
      _stack.pop_back();
      uint64_t k_ = _f.k_;
      uint64_t e_ = _f.e_;
      _result =
          List<std::pair<uint64_t, std::pair<std::optional<uint64_t>,
                                             std::optional<uint64_t>>>>::cons(
              std::make_pair(k_,
                             std::make_pair(std::optional<uint64_t>(),
                                            std::make_optional<uint64_t>(e_))),
              std::move(_result));
    } else if (std::holds_alternative<_after_combine_in_true>(_popped)) {
      auto _f = std::move(std::get<_after_combine_in_true>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      uint64_t e = _f.e;
      _result =
          List<std::pair<uint64_t, std::pair<std::optional<uint64_t>,
                                             std::optional<uint64_t>>>>::cons(
              std::make_pair(k, std::make_pair(std::make_optional<uint64_t>(e),
                                               std::optional<uint64_t>())),
              std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_combine_in_true_2>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      uint64_t e = _f.e;
      uint64_t e_ = _f.e_;
      _result =
          List<std::pair<uint64_t, std::pair<std::optional<uint64_t>,
                                             std::optional<uint64_t>>>>::cons(
              std::make_pair(k,
                             std::make_pair(std::make_optional<uint64_t>(e),
                                            std::make_optional<uint64_t>(e_))),
              std::move(_result));
    }
  }
  return _result;
}
