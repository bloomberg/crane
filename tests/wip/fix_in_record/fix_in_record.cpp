#include <fix_in_record.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>

std::shared_ptr<FixInRecord::fn_box>
FixInRecord::make_box(const unsigned int n) {
  unsigned int base = (n * 3u);
  std::function<unsigned int(unsigned int)> add;
  add = [&](unsigned int x) -> unsigned int {
    if (x <= 0) {
      return base;
    } else {
      unsigned int x_ = x - 1;
      return (add(x_) + 1);
    }
  };
  return std::make_shared<FixInRecord::fn_box>(fn_box{base, add});
}
