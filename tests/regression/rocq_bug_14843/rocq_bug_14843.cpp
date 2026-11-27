#include "rocq_bug_14843.h"

void RocqBug14843::M::f1() {}

void RocqBug14843::M::f2() { f1(); }

void RocqBug14843::M::f1_() { f1(); }

void RocqBug14843::M::f2_() { f1(); }
