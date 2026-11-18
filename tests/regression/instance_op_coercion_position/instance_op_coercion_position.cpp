#include "instance_op_coercion_position.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: generated program, shrunk by ephyra and delta-reduced
/// (unrelated-looking declarations kept are needed for the trigger).
///
/// In a module instantiating a module type with t := bool, op applies the class
/// method mop to two lets (one binding an unused inr): under CRANE_CHECK_IR=1
/// "coercion position: a coercion in M3_2.op is lowered against none, the
/// plan's position is M3_2.t".
InstanceOpCoercionPosition::M3_2::t
InstanceOpCoercionPosition::M3_2::op(bool u18, bool v19) {
  return mon_bool::mop(
      [&]() {
        InstanceOpCoercionPosition::M3_2::t x20 = u18;
        return x20;
      }(),
      v19);
}
