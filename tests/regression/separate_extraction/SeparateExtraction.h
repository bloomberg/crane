#ifndef INCLUDED_SEPARATEEXTRACTION
#define INCLUDED_SEPARATEEXTRACTION

#include <utility>

namespace SeparateExtraction {

uint64_t sep_add(uint64_t _x0, uint64_t _x1);
enum class Color { RED, GREEN, BLUE };
uint64_t color_to_nat(Color c);

} // namespace SeparateExtraction

#endif // INCLUDED_SEPARATEEXTRACTION
