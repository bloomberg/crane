#include "constraint_substitution_obj.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: generated program, shrunk by ephyra and delta-reduced
/// (unrelated-looking declarations kept are needed for the trigger).
///
/// A mutual fixpoint returning sum (st nat) (option tree) (with st A := nat ->
/// A * nat) through a local fixpoint over list (st pt): instantiating a
/// requires clause in theories/cpp/obj.h fails, "substitution into constraint
/// expression resulted in a non-constant expression".
uint64_t
ConstraintSubstitutionObj::tree_obs(const ConstraintSubstitutionObj::tree &t) {
  if (std::holds_alternative<typename ConstraintSubstitutionObj::tree::Leaf>(
          t.v())) {
    return UINT64_C(1);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename ConstraintSubstitutionObj::tree::Node>(t.v());
    auto _once1 =
        (((tree_obs(*a0) * UINT64_C(7)) + a1) + (tree_obs(*a2) * UINT64_C(3)));
    return (UINT64_C(10007) ? _once1 % UINT64_C(10007) : _once1);
  }
}

int64_t ConstraintSubstitutionObj::h2a(uint64_t) { return INT64_C(0); }

Sum<ConstraintSubstitutionObj::st<uint64_t>,
    std::optional<ConstraintSubstitutionObj::tree>>
ConstraintSubstitutionObj::h2b(uint64_t n36) {
  if (n36 <= 0) {
    if (List<uint64_t>::nil().template fold_left<bool>(
            [](bool acc37, uint64_t) { return mon_bool::mop(acc37, acc37); },
            [&]() -> bool {
              if (n36 <= 0) {
                return true;
              } else {
                uint64_t _x = n36 - 1;
                return true;
              }
            }())) {
      return Sum<ConstraintSubstitutionObj::st<uint64_t>,
                 std::optional<ConstraintSubstitutionObj::tree>>::inr(
          [&]() -> std::optional<ConstraintSubstitutionObj::tree> {
            if (n36 <= 0) {
              return std::optional<ConstraintSubstitutionObj::tree>();
            } else {
              uint64_t _x = n36 - 1;
              return std::make_optional<ConstraintSubstitutionObj::tree>(
                  tree::leaf());
            }
          }());
    } else {
      auto go41 =
          [&](const List<
              ConstraintSubstitutionObj::st<ConstraintSubstitutionObj::pt>> &l42,
              const Sum<ConstraintSubstitutionObj::st<uint64_t>,
                        std::optional<ConstraintSubstitutionObj::tree>> &acc43)
               -> Sum<ConstraintSubstitutionObj::st<uint64_t>,
                      std::optional<ConstraintSubstitutionObj::tree>> {
            // Loop replaces the tail recursion: each recursive call updates the
            // loop variables.
            Sum<ConstraintSubstitutionObj::st<uint64_t>,
                std::optional<ConstraintSubstitutionObj::tree>> _loop_acc43 =
                acc43;
            const List<
                ConstraintSubstitutionObj::st<ConstraintSubstitutionObj::pt>> *_loop_l42 =
                &l42;
            while (true) {
              if (std::holds_alternative<
                      typename List<ConstraintSubstitutionObj::st<
                          ConstraintSubstitutionObj::pt>>::Nil>(_loop_l42->v())) {
                return Sum<ConstraintSubstitutionObj::st<uint64_t>,
                           std::optional<ConstraintSubstitutionObj::tree>>::inr(
                    std::optional<ConstraintSubstitutionObj::tree>());
              } else {
                const auto &[_, a1] =
                    std::get<typename List<ConstraintSubstitutionObj::st<
                        ConstraintSubstitutionObj::pt>>::Cons>(_loop_l42->v());
                _loop_acc43 = [&]() -> Sum<
                    ConstraintSubstitutionObj::st<uint64_t>,
                    std::optional<ConstraintSubstitutionObj::tree>> {
                  if (n36 <= 0) {
                    return Sum<ConstraintSubstitutionObj::st<uint64_t>,
                               std::optional<ConstraintSubstitutionObj::tree>>::inl(
                        sret<uint64_t>(UINT64_C(7)));
                  } else {
                    uint64_t _x0 = n36 - 1;
                    return _loop_acc43;
                  }
                }();
                _loop_l42 = crane_raw(a1);
              }
            }
          };
      return go41(
          List<uint64_t>::nil().template flat_map<
              ConstraintSubstitutionObj::st<ConstraintSubstitutionObj::pt>>(
              [](uint64_t) {
                return List<ConstraintSubstitutionObj::st<
                    ConstraintSubstitutionObj::pt>>::nil();
              }),
          Sum<ConstraintSubstitutionObj::st<uint64_t>,
              std::optional<ConstraintSubstitutionObj::tree>>::inr(
              std::make_optional<ConstraintSubstitutionObj::tree>(tree::leaf())));
    }
  } else {
    uint64_t _x = n36 - 1;
    return Sum<ConstraintSubstitutionObj::st<uint64_t>,
               std::optional<ConstraintSubstitutionObj::tree>>::inr(
        std::make_optional<ConstraintSubstitutionObj::tree>(tree::leaf()));
  }
}
