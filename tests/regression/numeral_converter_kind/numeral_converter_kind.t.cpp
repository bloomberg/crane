#include <numeral_converter_kind.h>
#include <cassert>

int main() {
    assert(NumeralConverterKind::z_minus_one == -1);
    assert(NumeralConverterKind::z_minus_ten_hex == -10);
    assert(NumeralConverterKind::z_plus_twelve == 12);
    assert(NumeralConverterKind::z_uint == 42);
    assert(NumeralConverterKind::nat_big == 10000u);
    assert(NumeralConverterKind::nat_of_pos.has_value());
    assert(*NumeralConverterKind::nat_of_pos == 7u);
    assert(!NumeralConverterKind::nat_of_neg.has_value());
    return 0;
}
