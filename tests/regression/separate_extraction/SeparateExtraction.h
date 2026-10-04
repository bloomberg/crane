#ifndef INCLUDED_SEPARATEEXTRACTION
#define INCLUDED_SEPARATEEXTRACTION

#include <cstdint>
#include <utility>

namespace SeparateExtraction {

enum class Color;
uint64_t sep_add(uint64_t x0_, uint64_t x1_);
enum class Color { RED, GREEN, BLUE };
uint64_t color_to_nat(Color c);

} // namespace SeparateExtraction

#endif // INCLUDED_SEPARATEEXTRACTION
