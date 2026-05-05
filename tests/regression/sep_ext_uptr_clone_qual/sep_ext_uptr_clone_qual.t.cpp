#include "SepExtUptrCloneQual.h"

#include <cassert>

struct IntOrd {
  using t = int;
};
static_assert(SepExtUptrCloneQual::OrderedType<IntOrd>);

int main() {
  using F = SepExtUptrCloneQual::FMap<IntOrd>;
  auto l = SepExtUptrCloneQual::MyList<std::pair<int, bool>>::mycons(
      {1, true},
      SepExtUptrCloneQual::MyList<std::pair<int, bool>>::mynil());
  auto tl = F::tail<bool>(l);
  using Nil = SepExtUptrCloneQual::MyList<std::pair<int, bool>>::Mynil;
  assert(std::holds_alternative<Nil>(tl.v()));
  return 0;
}
