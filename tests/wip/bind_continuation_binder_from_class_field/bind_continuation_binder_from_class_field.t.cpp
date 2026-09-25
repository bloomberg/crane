#include <cassert>
#include <bind_continuation_binder_from_class_field.h>

int main() {
  auto r = BindContinuationBinderFromClassField::run();
  (void)r;
  return 0;
}
