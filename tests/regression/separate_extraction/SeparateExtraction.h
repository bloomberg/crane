#ifndef INCLUDED_SEPARATEEXTRACTION
#define INCLUDED_SEPARATEEXTRACTION

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

namespace SeparateExtraction {

unsigned int sep_add(const unsigned int _x0, const unsigned int _x1);
enum class Color { e_RED, e_GREEN, e_BLUE };
unsigned int color_to_nat(const Color c);

} // namespace SeparateExtraction

#endif // INCLUDED_SEPARATEEXTRACTION
