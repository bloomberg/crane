// WIP: Enum constructors used as values inside functors must compile.
// They should be emitted as EnumType::e_CTOR, not as function calls.

#include "SepExtEnumAsValue.h"
#include "Datatypes.h"

struct MyParam {
  using Color = SepExtEnumAsValue::Color;
  static constexpr Color default_ = Color::e_RED;
};

int main() {
  using UC = SepExtEnumAsValue::UseColor<MyParam>;
  const auto c = UC::my_default();
  (void)c;
  const auto l = UC::color_list();
  (void)l;
  const bool r = UC::is_red(SepExtEnumAsValue::Color::e_GREEN);
  (void)r;
  return 0;
}
