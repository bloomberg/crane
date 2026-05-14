// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: function-type arguments in concept requires-expressions must
// qualify module member types.  Previously, (elt -> bool) in a requires
// block rendered as std::function<bool(elt)> instead of
// std::function<bool(typename M::elt)>.

#include "SepExtFunTypeQual.h"

#include <cassert>
#include <functional>
#include <vector>

struct MyS {
  using elt = int;
  using t = std::vector<int>;

  static bool for_all(std::function<bool(int)> f, std::vector<int> v) {
    for (auto x : v)
      if (!f(x)) return false;
    return true;
  }
  static bool exists_(std::function<bool(int)> f, std::vector<int> v) {
    for (auto x : v)
      if (f(x)) return true;
    return false;
  }
  static std::vector<int> filter(std::function<bool(int)> f, std::vector<int> v) {
    std::vector<int> out;
    for (auto x : v)
      if (f(x)) out.push_back(x);
    return out;
  }
};

static_assert(SepExtFunTypeQual::S<MyS>);

int main() {
  using MM = SepExtFunTypeQual::MyModule<MyS>;
  std::vector<int> v = {1, 2, 3};
  auto result = MM::test(v);
  assert(result == v);
  return 0;
}
