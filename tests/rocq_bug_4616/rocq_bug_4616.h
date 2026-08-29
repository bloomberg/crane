#ifndef INCLUDED_ROCQ_BUG_4616
#define INCLUDED_ROCQ_BUG_4616

#include <any>
#include <functional>

struct RocqBug4616 {
  enum class Foo_ { FOO };
  using foo = std::any;
  using f = std::function<std::any(Foo_)>;
};

#endif // INCLUDED_ROCQ_BUG_4616
