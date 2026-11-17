#pragma once

#include "fn.h"
#include "obj.h"

struct RocqBug4616 {
  enum class Foo_ { FOO };
  using foo = crane::obj;
  using f = crane::fn<crane::obj(Foo_)>;
};
