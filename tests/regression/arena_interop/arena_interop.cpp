#include "arena_interop.h"

Nat Interop::wrapper_size(const Interop::wrapper &w) {
  return w.w_tree.count();
}
