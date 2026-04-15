#include <record_erased_proof_fields.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int RecordErasedProofFieldsCase::kind_code(
    const RecordErasedProofFieldsCase::ItemKind k) {
  switch (k) {
  case ItemKind::e_KINDA: {
    return 0u;
  }
  case ItemKind::e_KINDB: {
    return 1u;
  }
  case ItemKind::e_KINDC: {
    return 2u;
  }
  case ItemKind::e_KINDD: {
    return 3u;
  }
  case ItemKind::e_KINDE: {
    return 4u;
  }
  case ItemKind::e_KINDF: {
    return 5u;
  }
  case ItemKind::e_KINDG: {
    return 6u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int RecordErasedProofFieldsCase::tag_code(
    const std::shared_ptr<RecordErasedProofFieldsCase::StoredTag> &t) {
  if (std::holds_alternative<
          typename RecordErasedProofFieldsCase::StoredTag::TagPrimary>(
          t->v())) {
    const auto &_m = *std::get_if<
        typename RecordErasedProofFieldsCase::StoredTag::TagPrimary>(&t->v());
    return (10u + kind_code(_m.d_a0));
  } else {
    const auto &_m = *std::get_if<
        typename RecordErasedProofFieldsCase::StoredTag::TagSecondary>(&t->v());
    return (20u + kind_code(_m.d_a0));
  }
}

__attribute__((pure)) unsigned int RecordErasedProofFieldsCase::bucket_code(
    const RecordErasedProofFieldsCase::TraceBucket b) {
  switch (b) {
  case TraceBucket::e_BUCKETA: {
    return 30u;
  }
  case TraceBucket::e_BUCKETB: {
    return 31u;
  }
  case TraceBucket::e_BUCKETC: {
    return 32u;
  }
  default:
    std::unreachable();
  }
}

std::shared_ptr<RecordErasedProofFieldsCase::StoredTag>
RecordErasedProofFieldsCase::bucket_to_tag(
    const RecordErasedProofFieldsCase::TraceBucket b) {
  switch (b) {
  case TraceBucket::e_BUCKETA: {
    return StoredTag::tagsecondary(ItemKind::e_KINDD);
  }
  case TraceBucket::e_BUCKETB: {
    return StoredTag::tagsecondary(ItemKind::e_KINDE);
  }
  case TraceBucket::e_BUCKETC: {
    return StoredTag::tagsecondary(ItemKind::e_KINDB);
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int
RecordErasedProofFieldsCase::left_kind_code_of(
    const std::shared_ptr<RecordErasedProofFieldsCase::PrimaryRecord> &r) {
  return kind_code(r->primary_left_kind);
}

__attribute__((pure)) unsigned int
RecordErasedProofFieldsCase::right_kind_code_of(
    const std::shared_ptr<RecordErasedProofFieldsCase::PrimaryRecord> &r) {
  return kind_code(r->primary_right_kind);
}

__attribute__((pure)) unsigned int RecordErasedProofFieldsCase::tag_code_of(
    const std::shared_ptr<RecordErasedProofFieldsCase::PrimaryRecord> &r) {
  return tag_code(r->primary_tag);
}

__attribute__((pure)) unsigned int RecordErasedProofFieldsCase::bucket_code_of(
    const std::shared_ptr<RecordErasedProofFieldsCase::ErasedProofRecord> &r) {
  return bucket_code(r->erased_bucket);
}

std::shared_ptr<List<unsigned int>> RecordErasedProofFieldsCase::trace_codes_of(
    const std::shared_ptr<RecordErasedProofFieldsCase::PrimaryRecord> &primary,
    const std::shared_ptr<RecordErasedProofFieldsCase::ErasedProofRecord>
        &erased) {
  return List<unsigned int>::cons(
      left_kind_code_of(primary),
      List<unsigned int>::cons(
          right_kind_code_of(primary),
          List<unsigned int>::cons(
              tag_code_of(primary),
              List<unsigned int>::cons(
                  bucket_code_of(erased),
                  List<unsigned int>::cons(
                      tag_code(bucket_to_tag(erased->erased_bucket)),
                      List<unsigned int>::nil())))));
}

__attribute__((pure)) unsigned int
RecordErasedProofFieldsCase::trace_checksum_of(
    const std::shared_ptr<RecordErasedProofFieldsCase::PrimaryRecord> &primary,
    const std::shared_ptr<RecordErasedProofFieldsCase::ErasedProofRecord>
        &erased) {
  return trace_codes_of(primary, erased)
      ->template fold_left<unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          0u);
}
