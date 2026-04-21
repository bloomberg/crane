#include <fix_in_record.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>

std::shared_ptr<FixInRecord::fn_box>
FixInRecord::make_box(const unsigned int n) {
  unsigned int base = (n * 3u);
  auto add = std::make_shared<std::function<unsigned int(unsigned int)>>();
  *add = [=](unsigned int x) mutable -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return ((*add)(x_) + 1);
    }
  };
  return std::make_shared<FixInRecord::fn_box>(fn_box{base, *add});
}
