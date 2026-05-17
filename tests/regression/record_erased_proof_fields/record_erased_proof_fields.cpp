#include "record_erased_proof_fields.h"

unsigned int RecordErasedProofFieldsCase::kind_code(
    RecordErasedProofFieldsCase::ItemKind k) {
  switch (k) {
  case ItemKind::KINDA: {
    return 0u;
  }
  case ItemKind::KINDB: {
    return 1u;
  }
  case ItemKind::KINDC: {
    return 2u;
  }
  case ItemKind::KINDD: {
    return 3u;
  }
  case ItemKind::KINDE: {
    return 4u;
  }
  case ItemKind::KINDF: {
    return 5u;
  }
  case ItemKind::KINDG: {
    return 6u;
  }
  default:
    std::unreachable();
  }
}

unsigned int RecordErasedProofFieldsCase::tag_code(
    const RecordErasedProofFieldsCase::StoredTag &t) {
  if (std::holds_alternative<
          typename RecordErasedProofFieldsCase::StoredTag::TagPrimary>(t.v())) {
    const auto &[a0] =
        std::get<typename RecordErasedProofFieldsCase::StoredTag::TagPrimary>(
            t.v());
    return (10u + kind_code(a0));
  } else {
    const auto &[a0] =
        std::get<typename RecordErasedProofFieldsCase::StoredTag::TagSecondary>(
            t.v());
    return (20u + kind_code(a0));
  }
}

unsigned int RecordErasedProofFieldsCase::bucket_code(
    RecordErasedProofFieldsCase::TraceBucket b) {
  switch (b) {
  case TraceBucket::BUCKETA: {
    return 30u;
  }
  case TraceBucket::BUCKETB: {
    return 31u;
  }
  case TraceBucket::BUCKETC: {
    return 32u;
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

unsigned int RecordErasedProofFieldsCase::left_kind_code_of(
    const RecordErasedProofFieldsCase::PrimaryRecord &r) {
  return kind_code(r.primary_left_kind);
}

unsigned int RecordErasedProofFieldsCase::right_kind_code_of(
    const RecordErasedProofFieldsCase::PrimaryRecord &r) {
  return kind_code(r.primary_right_kind);
}

unsigned int RecordErasedProofFieldsCase::tag_code_of(
    const RecordErasedProofFieldsCase::PrimaryRecord &r) {
  return tag_code(r.primary_tag);
}

unsigned int RecordErasedProofFieldsCase::bucket_code_of(
    const RecordErasedProofFieldsCase::ErasedProofRecord &r) {
  return bucket_code(r.erased_bucket);
}

List<unsigned int> RecordErasedProofFieldsCase::trace_codes_of(
    const RecordErasedProofFieldsCase::PrimaryRecord &primary,
    const RecordErasedProofFieldsCase::ErasedProofRecord &erased) {
  return List<unsigned int>::cons(
      left_kind_code_of(primary),
      List<unsigned int>::cons(
          right_kind_code_of(primary),
          List<unsigned int>::cons(
              tag_code_of(primary),
              List<unsigned int>::cons(
                  bucket_code_of(erased),
                  List<unsigned int>::cons(
                      tag_code(bucket_to_tag(erased.erased_bucket)),
                      List<unsigned int>::nil())))));
}

unsigned int RecordErasedProofFieldsCase::trace_checksum_of(
    const RecordErasedProofFieldsCase::PrimaryRecord &primary,
    const RecordErasedProofFieldsCase::ErasedProofRecord &erased) {
  return trace_codes_of(primary, erased)
      .template fold_left<unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          0u);
}
