// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>

#include "pulse_parse_certificate.h"

int main() {
  assert(PulseParseCertificateCase::sample_certificate_consistent);
  assert(PulseParseCertificateCase::sample_certificate_base == 1u);
  assert(PulseParseCertificateCase::sample_certificate_first_active == 1u);
  assert(PulseParseCertificateCase::sample_certificate_last_active == 4u);
  assert(PulseParseCertificateCase::sample_certificate_class_count == 5u);
  return 0;
}
