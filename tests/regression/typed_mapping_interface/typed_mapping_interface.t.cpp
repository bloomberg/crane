#include <typed_mapping_interface.h>
#include <cassert>
#include <cstdint>
#include <type_traits>

// Both units spell Meter as the Narrow mapping's std::uint32_t.
static_assert(std::is_same_v<decltype(Use::quad(std::uint32_t{1})), std::uint32_t>);
static_assert(std::is_same_v<decltype(Lib::double_(std::uint32_t{1})), std::uint32_t>);

int main() {
  assert(Use::answer == 12);
  assert(Use::quad(std::uint32_t{5}) == 20);
  return 0;
}
