#include "branch_callables_curried_join.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Match branches producing two-argument function values, one a curried
/// lambda, the other a composed let-lambda (let cf .. in let cg .. in fun c
/// => cf (cg c)), bound by a beta-redex: the C++ declares the variable at
/// one branch's type and assigns the other ("no viable overloaded '='").
/// Remaining after d7cf5aaae (common crane::fn type for joined callables).
/// A match's branches now carry the slot into their tails, so the lambda
/// knows the Core type backing the two-parameter function it is written
/// against, and takes the parameter its body leaves to a partial
/// application.
uint64_t BranchCallablesCurriedJoin::t(const List<uint64_t> &l) {
  crane::fn<bool(uint64_t, BranchCallablesCurriedJoin::pt)> w;
  auto _cs = l.length();
  if (_cs <= 0) {
    w = [](uint64_t, BranchCallablesCurriedJoin::pt) { return true; };
  } else {
    uint64_t _x = _cs - 1;
    crane::fn<bool(bool, BranchCallablesCurriedJoin::pt)> cf =
        [](bool, BranchCallablesCurriedJoin::pt) { return false; };
    crane::fn<bool(uint64_t)> cg = [](uint64_t) { return true; };
    w = [=, cf = std::move(cf), cg = std::move(cg)](
        uint64_t c,
        const BranchCallablesCurriedJoin::pt &eta0_) {
      return cf(cg(c), eta0_);
    };
  }
  if (w(UINT64_C(0), pt{UINT64_C(0), true})) {
    return UINT64_C(1);
  } else {
    return UINT64_C(2);
  }
}

/// The same join as a fold_left step's result: the accumulator passes
/// through fold_left's type variable, so the step returns its curried
/// spelling, and so do both branches.
uint64_t BranchCallablesCurriedJoin::t2(const List<uint64_t> &l) {
  return l.template fold_left<crane::fn<uint64_t(int64_t, bool)>>(
      [](crane::fn<uint64_t(int64_t, bool)> acc, uint64_t x) -> crane::fn<
          uint64_t(int64_t, bool)> {
        if (x <= 0) {
          return [](int64_t, bool b) -> uint64_t {
            if (b) {
              return UINT64_C(1);
            } else {
              return UINT64_C(0);
            }
          };
        } else {
          uint64_t _x = x - 1;
          crane::fn<uint64_t(uint64_t, bool)> cf =
              [](uint64_t n, bool) { return n; };
          return [=, acc = std::move(acc), cf = std::move(cf)](int64_t z,
                                                               bool eta0_) {
            return cf(acc(z, false), eta0_);
          };
        }
      },
      [](int64_t, bool) { return UINT64_C(7); })(INT64_C(3), true);
}

uint64_t BranchCallablesCurriedJoin::v3(std::optional<uint64_t> x) {
  std::pair<uint64_t, crane::fn<uint64_t(uint64_t)>> p = [&]() {
    auto &&_sv = [&]() -> BranchCallablesCurriedJoin::tree {
      if (x.has_value()) {
        const uint64_t &o = *x;
        return tree::leaf().tins(o);
      } else {
        return tree::leaf();
      }
    }();
    if (std::holds_alternative<typename BranchCallablesCurriedJoin::tree::Leaf>(
            _sv.v())) {
      return std::make_pair(UINT64_C(0), crane::fn<uint64_t(uint64_t)>([](
                                             uint64_t) {
                                           return UINT64_C(0);
                                         }));
    } else {
      const auto &[_, a1, _] =
          std::get<typename BranchCallablesCurriedJoin::tree::Node>(_sv.v());
      return std::make_pair(a1, crane::fn<uint64_t(uint64_t)>([]() {
        auto go =
            [](List<uint64_t> l, crane::fn<uint64_t(uint64_t)> acc,
               uint64_t x0_)
                 -> uint64_t {
              // Loop replaces the tail recursion: each recursive call updates
              // the loop variables.
              List<uint64_t> _loop_l = std::move(l);
              while (true) {
                if (std::holds_alternative<typename List<uint64_t>::Nil>(
                        _loop_l.v_mut())) {
                  return acc(x0_);
                } else {
                  auto &[_, a4] =
                      std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
                  _loop_l = List<uint64_t>(*a4);
                }
              }
            };
        return [=](uint64_t _pa0) {
          return go(List<uint64_t>::nil(), [](uint64_t) { return UINT64_C(0); },
                    _pa0);
        };
      }()));
    }
  }();
  return (p.first + p.second(UINT64_C(1)));
}

uint64_t BranchCallablesCurriedJoin::f1(
    const BranchCallablesCurriedJoin::ptree<std::pair<uint64_t, uint64_t>> &,
    uint64_t x0_, const BranchCallablesCurriedJoin::tree &x1_) {
  return []() {
    auto go =
        [](List<bool> l,
           crane::fn<uint64_t(uint64_t, BranchCallablesCurriedJoin::tree)>,
           uint64_t, BranchCallablesCurriedJoin::tree)
             -> uint64_t {
          // Loop replaces the tail recursion: each recursive call updates the
          // loop variables.
          List<bool> _loop_l = std::move(l);
          while (true) {
            if (std::holds_alternative<typename List<bool>::Nil>(
                    _loop_l.v_mut())) {
              return UINT64_C(0);
            } else {
              auto &[_, a1] =
                  std::get<typename List<bool>::Cons>(_loop_l.v_mut());
              const List<bool> &a1_value = *a1;
              _loop_l = List<bool>(a1_value);
            }
          }
        };
    return [=](uint64_t _pa0, BranchCallablesCurriedJoin::tree _pa1) {
      return go(
          List<bool>::nil(),
          []() {
            crane::fn<uint64_t(BranchCallablesCurriedJoin::tree,
                               BranchCallablesCurriedJoin::tree)> cf =
                [](BranchCallablesCurriedJoin::tree,
                   BranchCallablesCurriedJoin::tree) { return UINT64_C(0); };
            crane::fn<BranchCallablesCurriedJoin::tree(uint64_t)> cg =
                [](uint64_t) { return tree::leaf(); };
            return [=, cf = std::move(cf), cg = std::move(cg)](
                uint64_t c,
                const BranchCallablesCurriedJoin::tree &eta0_) {
              return cf(cg(c), eta0_);
            };
          }(),
          _pa0,
          _pa1);
    };
  }()(x0_, x1_);
}

std::pair<uint64_t,
          crane::fn<String(BranchCallablesCurriedJoin::ptree<bool>, bool)>>
BranchCallablesCurriedJoin::v10(const List<uint64_t> &l) {
  return std::make_pair(
      UINT64_C(0), crane::fn<
                       String(BranchCallablesCurriedJoin::ptree<bool>, bool)>([
                       &]() -> crane::fn<
                       String(BranchCallablesCurriedJoin::ptree<bool>, bool)> {
                     auto &&_sv =
                         l.template map<BranchCallablesCurriedJoin::tree>(
                             [](uint64_t) { return tree::leaf(); });
                     if (std::holds_alternative<typename List<
                             BranchCallablesCurriedJoin::tree>::Nil>(_sv.v())) {
                       return [](BranchCallablesCurriedJoin::ptree<bool>,
                                 bool) { return String::emptystring(); };
                     } else {
                       crane::fn<String(uint64_t, bool)> cf =
                           [](uint64_t,
                              bool) {
                             return String::string0(
                                 Ascii::ascii0(true, false, false, false, false,
                                               true, true, false),
                                 String::emptystring());
                           };
                       return [=, cf = std::move(cf)](
                           BranchCallablesCurriedJoin::ptree<bool>,
                           bool eta0_) { return cf(UINT64_C(0), eta0_); };
                     }
                   }()));
}

uint64_t BranchCallablesCurriedJoin::v11(const List<uint64_t> &l) {
  return app2([&]() {
    auto _pa0 = v10(l);
    return [=](BranchCallablesCurriedJoin::ptree<bool> _x0,
               bool _x1)
                -> String { return _pa0.second(_x0, _x1); };
  }());
}

uint64_t BranchCallablesCurriedJoin::v12(const List<uint64_t> &l) {
  return app2(l.template map<BranchCallablesCurriedJoin::tree>(
      [](uint64_t) { return tree::leaf(); })
                  .template fold_left<
      crane::fn<String(BranchCallablesCurriedJoin::ptree<bool>, bool)>>(
      [](crane::fn<String(BranchCallablesCurriedJoin::ptree<bool>, bool)>,
         const BranchCallablesCurriedJoin::tree &x)
           -> crane::fn<String(BranchCallablesCurriedJoin::ptree<bool>, bool)> {
        if (std::holds_alternative<
                typename BranchCallablesCurriedJoin::tree::Leaf>(x.v())) {
          return [](BranchCallablesCurriedJoin::ptree<bool>,
                    bool) { return String::emptystring(); };
        } else {
          crane::fn<String(uint64_t, bool)> cf = [](uint64_t,
                                                    bool) {
            return String::string0(Ascii::ascii0(true, false, false, false,
                                                 false, true, true, false),
                                   String::emptystring());
          };
          return [=, cf = std::move(cf)](
              BranchCallablesCurriedJoin::ptree<bool>,
              bool eta0_) { return cf(UINT64_C(0), eta0_); };
        }
      },
      [](BranchCallablesCurriedJoin::ptree<bool>,
         bool) {
        return String::string0(
            Ascii::ascii0(false, true, false, true, true, true, true, false),
            String::emptystring());
      }));
}
