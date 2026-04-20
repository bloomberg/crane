#include <rocq_bug_4710.h>

#include <memory>
#include <type_traits>

__attribute__((pure)) unsigned int
RocqBug4710::bla(const std::shared_ptr<RocqBug4710::Foo2> &x) {
  return x->foo2p;
}

__attribute__((pure)) bool
RocqBug4710::bla_(const unsigned int,
                  const std::shared_ptr<RocqBug4710::Foo2> &x) {
  return x->foo2b;
}
