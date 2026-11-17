#include "custom_signature_type_include.h"

bool CustomSignatureTypeInclude::is_real(bool b) {
  return ((std::complex<double>(b ? 1.0 : 0.0, 0.0)).imag() == 0.0);
}
