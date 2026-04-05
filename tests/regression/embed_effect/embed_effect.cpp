#include <embed_effect.h>

#include <cstdint>
#include <embed_effect_helper.h>
#include <string>
#include <type_traits>
#include <variant>

int64_t bug_main() {
  bug_create("hello");
  return bug_read();
}
