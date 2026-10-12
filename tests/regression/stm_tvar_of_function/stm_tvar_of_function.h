#ifndef INCLUDED_STM_TVAR_OF_FUNCTION
#define INCLUDED_STM_TVAR_OF_FUNCTION

#include "fn.h"
#include <crane_itree.h>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <stm_adapter.h>
#include <system_error>
#include <utility>
#include <variant>

struct StmTvarOfFunction {
  static uint64_t fntv();
  static uint64_t created();
  static uint64_t fnw();
  static uint64_t written();
};

#endif // INCLUDED_STM_TVAR_OF_FUNCTION
