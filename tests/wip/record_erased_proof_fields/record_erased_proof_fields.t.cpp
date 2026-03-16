// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>

#include "record_erased_proof_fields.h"

int main()
{
    assert(RecordErasedProofFieldsCase::left_kind_code_of(
               RecordErasedProofFieldsCase::sample_primary_record) == 2u);
    assert(RecordErasedProofFieldsCase::right_kind_code_of(
               RecordErasedProofFieldsCase::sample_primary_record) == 4u);
    assert(RecordErasedProofFieldsCase::tag_code_of(
               RecordErasedProofFieldsCase::sample_primary_record) == 12u);
    assert(RecordErasedProofFieldsCase::bucket_code_of(
               RecordErasedProofFieldsCase::sample_erased_proof_record) == 32u);
    assert(RecordErasedProofFieldsCase::sample_left_kind_code == 2u);
    assert(RecordErasedProofFieldsCase::sample_right_kind_code == 4u);
    assert(RecordErasedProofFieldsCase::sample_tag_code == 12u);
    assert(RecordErasedProofFieldsCase::sample_bucket_code == 32u);
    assert(RecordErasedProofFieldsCase::trace_checksum_of(
               RecordErasedProofFieldsCase::sample_primary_record,
               RecordErasedProofFieldsCase::sample_erased_proof_record) == 71u);
    assert(RecordErasedProofFieldsCase::sample_trace_checksum == 71u);
    return 0;
}
