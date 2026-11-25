#include <template_param_redef.h>

int main() {
  M::use<int>(std::monostate{});
  return 0;
}
