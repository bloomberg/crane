#ifndef INCLUDED_ROCQ_BUG_4616
#define INCLUDED_ROCQ_BUG_4616

#include "fn.h"
#include "obj.h"
#include <any>

struct RocqBug4616 {
  enum class Foo_ { FOO };
  using foo = crane::obj;
  using f = crane::fn<crane::obj(Foo_)>;
};

#endif // INCLUDED_ROCQ_BUG_4616
