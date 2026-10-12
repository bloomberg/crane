#ifndef INCLUDED_EVENT_SUM_ALIAS
#define INCLUDED_EVENT_SUM_ALIAS

#include "obj.h"
#include <chrono>
#include <crane_itree.h>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <optional>
#include <string>
#include <system_error>

struct EventSumAlias {
  template <typename x = void>
  using bigE = Sum1 << crane::obj >
      , Sum1 << crane::obj >, <crane::obj>, crane::obj >, x > ;
  static uint64_t go();
};

#endif // INCLUDED_EVENT_SUM_ALIAS
