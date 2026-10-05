#include "rocq_bug_14843.h"

void RocqBug14843::M::f1(Unit) { return; }

void RocqBug14843::M::f2(Unit _x) {
  f1(_x);
  return;
}

void RocqBug14843::M::f1_(Unit _x) {
  f1(_x);
  return;
}

void RocqBug14843::M::f2_(Unit _x) {
  f1(_x);
  return;
}
