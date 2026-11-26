#include "function_alias_spelling.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: generated programs, shrunk by ephyra and reduced by
/// hand.
///
/// A function type behind a definition (st A := nat -> A * nat) was
/// spelled two ways: unfolded, a function of the arrows it hides, at some
/// sites, and kept, st<A>, at others.  Where the two met the C++ did not
/// compile: a parameter typed nat * nat -> st Z passed on from a match
/// ("no viable conversion from 'const fn<st<int64_t> (pair)>' to
/// 'fn<pair<int64_t,uint64_t> (pair, uint64_t)>'"), a composed let-lambda
/// returning st bool, and a local fixpoint over list (st bool).
FunctionAliasSpelling::tree FunctionAliasSpelling::g2(
    const FunctionAliasSpelling::tree &t,
    const crane::fn<
        FunctionAliasSpelling::st<int64_t>(std::pair<uint64_t, uint64_t>)> &a) {
  if (std::holds_alternative<typename FunctionAliasSpelling::tree::Leaf>(t.v())) {
    return tree::leaf();
  } else {
    const auto &[l0, v_1, _] =
        std::get<typename FunctionAliasSpelling::tree::Node>(t.v());
    const FunctionAliasSpelling::tree &l0_value = *l0;
    return g2(l0_value, [&]() -> crane::fn<FunctionAliasSpelling::st<int64_t>(
                            std::pair<uint64_t, uint64_t>)> {
                          if (v_1 <= 0) {
                            return a;
                          } else {
                            uint64_t _x0 = v_1 - 1;
                            return [](std::pair<uint64_t,
                                                uint64_t>) {
                              return sret<int64_t>(INT64_C(0));
                            };
                          }
                        }());
  }
}

/// g2 with its parameter observed at the leaf.
int64_t
FunctionAliasSpelling::g2z(const FunctionAliasSpelling::tree &t,
                           const crane::fn<FunctionAliasSpelling::st<int64_t>(
                               std::pair<uint64_t, uint64_t>)> &a) {
  if (std::holds_alternative<typename FunctionAliasSpelling::tree::Leaf>(t.v())) {
    return crane::apply2(a, std::make_pair(UINT64_C(0), UINT64_C(0)),
                         UINT64_C(0))
               .first;
  } else {
    const auto &[l0, v_1, _] =
        std::get<typename FunctionAliasSpelling::tree::Node>(t.v());
    const FunctionAliasSpelling::tree &l0_value = *l0;
    return g2z(l0_value, [&]() -> crane::fn<FunctionAliasSpelling::st<int64_t>(
                             std::pair<uint64_t, uint64_t>)> {
                           if (v_1 <= 0) {
                             return a;
                           } else {
                             uint64_t _x0 = v_1 - 1;
                             return [](std::pair<uint64_t,
                                                 uint64_t>) {
                               return sret<int64_t>(INT64_C(0));
                             };
                           }
                         }());
  }
}

FunctionAliasSpelling::st<bool>
FunctionAliasSpelling::sf2(FunctionAliasSpelling::st<bool> a6,
                           const List<uint64_t> &x0_) {
  crane::fn<FunctionAliasSpelling::st<bool>(std::pair<uint64_t, String>)> cf =
      [=, a6 = std::move(a6)](std::pair<uint64_t, String>) { return a6; };
  crane::fn<std::pair<uint64_t, String>(List<uint64_t>)> cg =
      [](List<uint64_t>) {
        return std::make_pair(UINT64_C(0), String::emptystring());
      };
  return cf(cg(x0_));
}
