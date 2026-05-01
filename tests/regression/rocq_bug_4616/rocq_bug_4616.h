#ifndef INCLUDED_ROCQ_BUG_4616
#define INCLUDED_ROCQ_BUG_4616

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

struct RocqBug4616 {
  enum class Foo_ { e_FOO };
  using foo = std::any;
  using f = std::function<std::any(Foo_)>;
};

#endif // INCLUDED_ROCQ_BUG_4616
