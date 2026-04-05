#include <embed_effect.h>

#include <cstdint>
#include <embed_effect_helper.h>
#include <string>
#include <type_traits>
#include <variant>

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
