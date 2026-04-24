#include <rocq_bug_14843.h>

#include <functional>
#include <type_traits>

void RocqBug14843::M::f1(const Unit) { return; }

void RocqBug14843::M::f2(const Unit) { return; }

void RocqBug14843::M::f1_(const Unit) { return; }

void RocqBug14843::M::f2_(const Unit) { return; }
