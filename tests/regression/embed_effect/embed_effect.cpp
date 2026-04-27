#include <embed_effect.h>

void bug_create(const std::string title) {
  {
    bug_create_impl(title);
    return;
  }
}

int64_t bug_main() {
  bug_create("hello");
  return bug_read();
}
