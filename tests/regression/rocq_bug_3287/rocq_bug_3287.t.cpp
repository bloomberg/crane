// Rocq bug #3287: extraction of module with logical parts (I,I)
// A module containing a logical value like (I,I) : (True * True) : Prop
// used to fail with "The informative inductive type prod has a Prop
// instance.", as Rocq's OCaml extraction does.  The proof is now erased whole;
// the bar values from both modules extract.

#include <rocq_bug_3287.h>

#include <cassert>

int main() {
  assert(RocqBug3287::bar1 == Bool0::TRUE_);
  assert(RocqBug3287::bar2 == Bool0::TRUE_);
  return 0;
}
