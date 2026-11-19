#include "mutual_st_frame_plan_binder.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: generated program, shrunk by ephyra and delta-reduced
/// (unrelated-looking declarations kept are needed for the trigger).
///
/// A mutual fixpoint returning st (ptree nat) through a local fixpoint seeded
/// with the recursive call, next to a fold with nested non-tail local
/// fixpoints: CRANE_CHECK_IR=1 reports "frame plan: a binder the recursion plan
/// finds live across a call has no local in scope standing for it".
MutualStFramePlanBinder::st<MutualStFramePlanBinder::ptree<uint64_t>>
MutualStFramePlanBinder::h4a(const List<MutualStFramePlanBinder::tree> &n50) {
  // Explicit stack replaces the non-tail recursion of h4a: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<MutualStFramePlanBinder::tree> *n50;
  };

  struct _call_go65 {
    MutualStFramePlanBinder::st<MutualStFramePlanBinder::ptree<uint64_t>> _x0;
    List<std::pair<bool, MutualStFramePlanBinder::tree>> l66;
    std::shared_ptr<List<MutualStFramePlanBinder::tree>> a1;
  };

  struct _after_h4a_in_Cons {
    std::shared_ptr<List<MutualStFramePlanBinder::tree>> a1;
  };

  using _frame = std::variant<_call, _call_go65, _after_h4a_in_Cons>;
  MutualStFramePlanBinder::st<MutualStFramePlanBinder::ptree<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&n50});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<MutualStFramePlanBinder::tree> &n50 = *_f.n50;
      if (std::holds_alternative<
              typename List<MutualStFramePlanBinder::tree>::Nil>(n50.v())) {
        _result = sret<MutualStFramePlanBinder::ptree<uint64_t>>(
            ptree<uint64_t>::pleaf());
      } else {
        const auto &[_, a1] =
            std::get<typename List<MutualStFramePlanBinder::tree>::Cons>(
                n50.v());
        _stack.emplace_back(_after_h4a_in_Cons{a1});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else if (std::holds_alternative<_call_go65>(_popped)) {
      auto _f = std::move(std::get<_call_go65>(_popped));
      _stack.pop_back();
      const MutualStFramePlanBinder::st<
          MutualStFramePlanBinder::ptree<uint64_t>> &_x0 = _f._x0;
      const List<std::pair<bool, MutualStFramePlanBinder::tree>> &l66 = _f.l66;
      std::shared_ptr<List<MutualStFramePlanBinder::tree>> a1 =
          std::move(_f.a1);
      if (std::holds_alternative<typename List<
              std::pair<bool, MutualStFramePlanBinder::tree>>::Nil>(l66.v())) {
        _stack.emplace_back(_call{crane_raw(a1)});
      } else {
        const auto &[_, a10] =
            std::get<typename List<
                std::pair<bool, MutualStFramePlanBinder::tree>>::Cons>(l66.v());
        _stack.emplace_back(
            _call_go65{sret<MutualStFramePlanBinder::ptree<uint64_t>>(
                ptree<uint64_t>::pleaf()),
                       *a10, std::move(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_h4a_in_Cons>(_popped));
      _stack.pop_back();
      std::shared_ptr<List<MutualStFramePlanBinder::tree>> a1 =
          std::move(_f.a1);
      _stack.emplace_back(_call_go65{
          std::move(_result),
          List<std::pair<bool, MutualStFramePlanBinder::tree>>::nil(), a1});
    }
  }
  return _result;
}

uint64_t
MutualStFramePlanBinder::h4b(const List<MutualStFramePlanBinder::tree> &n76) {
  if (std::holds_alternative<typename List<MutualStFramePlanBinder::tree>::Nil>(
          n76.v())) {
    return UINT64_C(9);
  } else {
    return List<std::pair<uint64_t, MutualStFramePlanBinder::pt>>::cons(
        std::make_pair(UINT64_C(7), pt{UINT64_C(6), true}),
        List<std::pair<uint64_t, MutualStFramePlanBinder::pt>>::cons(
            std::make_pair(UINT64_C(5), pt{UINT64_C(0), true}),
            List<std::pair<uint64_t,
                           MutualStFramePlanBinder::pt>>::nil()))
               .template fold_left<uint64_t>(
        [](uint64_t,
           std::pair<uint64_t,
                     MutualStFramePlanBinder::pt>) {
          return mconcat<MutualStFramePlanBinder::mon_nat, uint64_t>(
              List<uint64_t>::cons(
                  UINT64_C(252),
                  List<uint64_t>::cons(
                      UINT64_C(8), List<uint64_t>::cons(
                                       UINT64_C(42),
                                       List<uint64_t>::cons(
                                           UINT64_C(5),
                                           List<uint64_t>::nil())))));
        },
        []() {
          auto go89 =
              [](const List<Sum<uint64_t, uint64_t>> &l90,
                 uint64_t acc91)
                   -> uint64_t {
                // Loop replaces the tail recursion: each recursive call updates
                // the loop variables.
                uint64_t _loop_acc91 = acc91;
                const List<Sum<uint64_t, uint64_t>> *_loop_l90 = &l90;
                while (true) {
                  if (std::holds_alternative<
                          typename List<Sum<uint64_t, uint64_t>>::Nil>(
                          _loop_l90->v())) {
                    auto go94 =
                        [](const List<bool> &l95, uint64_t acc96) -> uint64_t {
                          // Loop replaces the tail recursion: each recursive
                          // call updates the loop variables.
                          const List<bool> *_loop_l95 = &l95;
                          while (true) {
                            if (std::holds_alternative<typename List<bool>::Nil>(
                                    _loop_l95->v())) {
                              return acc96;
                            } else {
                              const auto &[_, a10] =
                                  std::get<typename List<bool>::Cons>(
                                      _loop_l95->v());
                              _loop_l95 = crane_raw(a10);
                            }
                          }
                        };
                    return go94(List<bool>::cons(
                        true,
                        List<bool>::cons(
                            true, List<bool>::cons(false, List<bool>::nil()))),
                                _loop_acc91);
                  } else {
                    const auto &[_, a3] =
                        std::get<typename List<Sum<uint64_t, uint64_t>>::Cons>(
                            _loop_l90->v());
                    _loop_acc91 = UINT64_C(232);
                    _loop_l90 = crane_raw(a3);
                  }
                }
              };
          return go89(List<Sum<uint64_t, uint64_t>>::cons(
              Sum<uint64_t, uint64_t>::inr(UINT64_C(6)),
              List<Sum<uint64_t, uint64_t>>::nil()),
                      UINT64_C(10));
        }());
  }
}
