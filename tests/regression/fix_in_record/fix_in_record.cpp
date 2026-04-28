#include <fix_in_record.h>

__attribute__((pure)) FixInRecord::fn_box
FixInRecord::make_box(const unsigned int &n) {
  unsigned int base = (n * 3u);
  auto add_impl = [=](auto &_self_add, unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return (_self_add(_self_add, x_) + 1);
    }
  };
  auto add = [=](unsigned int x) mutable -> unsigned int {
    return add_impl(add_impl, x);
  };
  return fn_box{base, add};
}
