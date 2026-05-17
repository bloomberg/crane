#include "rocq_bug_4710.h"

uint64_t RocqBug4710::bla(const RocqBug4710::Foo2 &x) { return x.foo2p; }

bool RocqBug4710::bla_(uint64_t, const RocqBug4710::Foo2 &x) { return x.foo2b; }
