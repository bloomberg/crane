#include "embed_effect.h"

template <typename T1> void bug_create(std::string title) {
  {
    bug_create_impl(std::move(title));
    return;
  }
}

int64_t bug_main() {
  bug_create("hello");
  return bug_read<void>();
}
