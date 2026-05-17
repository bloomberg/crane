#ifndef INCLUDED_SEPARATEEXTRACTION
#define INCLUDED_SEPARATEEXTRACTION

#include <utility>

namespace SeparateExtraction {

unsigned int sep_add(unsigned int _x0, unsigned int _x1);
enum class Color { RED, GREEN, BLUE };
unsigned int color_to_nat(Color c);

} // namespace SeparateExtraction

#endif // INCLUDED_SEPARATEEXTRACTION
