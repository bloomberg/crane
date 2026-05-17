#include "record_erased_proof_fields.h"

uint64_t RecordErasedProofFieldsCase::kind_code(
    RecordErasedProofFieldsCase::ItemKind k) {
  switch (k) {
  case ItemKind::KINDA: {
    return UINT64_C(0);
  }
  case ItemKind::KINDB: {
    return UINT64_C(1);
  }
  case ItemKind::KINDC: {
    return UINT64_C(2);
  }
  case ItemKind::KINDD: {
    return UINT64_C(3);
  }
  case ItemKind::KINDE: {
    return UINT64_C(4);
  }
  case ItemKind::KINDF: {
    return UINT64_C(5);
  }
  case ItemKind::KINDG: {
    return UINT64_C(6);
  }
  default:
    std::unreachable();
  }
}

uint64_t RecordErasedProofFieldsCase::tag_code(
    const RecordErasedProofFieldsCase::StoredTag &t) {
  if (std::holds_alternative<
          typename RecordErasedProofFieldsCase::StoredTag::TagPrimary>(t.v())) {
    const auto &[a0] =
        std::get<typename RecordErasedProofFieldsCase::StoredTag::TagPrimary>(
            t.v());
    return (UINT64_C(10) + kind_code(a0));
  } else {
    const auto &[a0] =
        std::get<typename RecordErasedProofFieldsCase::StoredTag::TagSecondary>(
            t.v());
    return (UINT64_C(20) + kind_code(a0));
  }
}

uint64_t RecordErasedProofFieldsCase::bucket_code(
    RecordErasedProofFieldsCase::TraceBucket b) {
  switch (b) {
  case TraceBucket::BUCKETA: {
    return UINT64_C(30);
  }
  case TraceBucket::BUCKETB: {
    return UINT64_C(31);
  }
  case TraceBucket::BUCKETC: {
    return UINT64_C(32);
  }
  default:
    std::unreachable();
  }
}

RecordErasedProofFieldsCase::StoredTag
RecordErasedProofFieldsCase::bucket_to_tag(
    RecordErasedProofFieldsCase::TraceBucket b) {
  switch (b) {
  case TraceBucket::BUCKETA: {
    return StoredTag::tagsecondary(ItemKind::KINDD);
  }
  case TraceBucket::BUCKETB: {
    return StoredTag::tagsecondary(ItemKind::KINDE);
  }
  case TraceBucket::BUCKETC: {
    return StoredTag::tagsecondary(ItemKind::KINDB);
  }
  default:
    std::unreachable();
  }
}

uint64_t RecordErasedProofFieldsCase::left_kind_code_of(
    const RecordErasedProofFieldsCase::PrimaryRecord &r) {
  return kind_code(r.primary_left_kind);
}

uint64_t RecordErasedProofFieldsCase::right_kind_code_of(
    const RecordErasedProofFieldsCase::PrimaryRecord &r) {
  return kind_code(r.primary_right_kind);
}

uint64_t RecordErasedProofFieldsCase::tag_code_of(
    const RecordErasedProofFieldsCase::PrimaryRecord &r) {
  return tag_code(r.primary_tag);
}

uint64_t RecordErasedProofFieldsCase::bucket_code_of(
    const RecordErasedProofFieldsCase::ErasedProofRecord &r) {
  return bucket_code(r.erased_bucket);
}

List<uint64_t> RecordErasedProofFieldsCase::trace_codes_of(
    const RecordErasedProofFieldsCase::PrimaryRecord &primary,
    const RecordErasedProofFieldsCase::ErasedProofRecord &erased) {
  return List<uint64_t>::cons(
      left_kind_code_of(primary),
      List<uint64_t>::cons(
          right_kind_code_of(primary),
          List<uint64_t>::cons(
              tag_code_of(primary),
              List<uint64_t>::cons(
                  bucket_code_of(erased),
                  List<uint64_t>::cons(
                      tag_code(bucket_to_tag(erased.erased_bucket)),
                      List<uint64_t>::nil())))));
}

uint64_t RecordErasedProofFieldsCase::trace_checksum_of(
    const RecordErasedProofFieldsCase::PrimaryRecord &primary,
    const RecordErasedProofFieldsCase::ErasedProofRecord &erased) {
  return trace_codes_of(primary, erased)
      .template fold_left<uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          UINT64_C(0));
}
