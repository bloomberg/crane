#ifndef INCLUDED_STM_TVAR_OF_FUNCTION
#define INCLUDED_STM_TVAR_OF_FUNCTION

#include "fn.h"
#include "shared_block.h"
#include <cstdint>
#include <stm_adapter.h>
#include <utility>
#include <variant>
static_assert(crane::rc_is_atomic,
              "this unit runs on several threads, but a header included before "
              "it chose CRANE_NON_ATOMIC_RC");

struct StmTvarOfFunction {
  static uint64_t fntv();
  static uint64_t created();
  static uint64_t fnw();
  static uint64_t written();
};

#endif // INCLUDED_STM_TVAR_OF_FUNCTION
