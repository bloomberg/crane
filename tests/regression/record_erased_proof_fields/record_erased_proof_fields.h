#ifndef INCLUDED_RECORD_ERASED_PROOF_FIELDS
#define INCLUDED_RECORD_ERASED_PROOF_FIELDS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).template fold_left<T1>(f, f(a0, d_a0));
    }
  }
};

struct RecordErasedProofFieldsCase {
  enum class ItemKind {
    e_KINDA,
    e_KINDB,
    e_KINDC,
    e_KINDD,
    e_KINDE,
    e_KINDF,
    e_KINDG
  };

  template <typename T1>
  static T1 ItemKind_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                          const T1 f3, const T1 f4, const T1 f5,
                          const ItemKind i) {
    switch (i) {
    case ItemKind::e_KINDA: {
      return f;
    }
    case ItemKind::e_KINDB: {
      return f0;
    }
    case ItemKind::e_KINDC: {
      return f1;
    }
    case ItemKind::e_KINDD: {
      return f2;
    }
    case ItemKind::e_KINDE: {
      return f3;
    }
    case ItemKind::e_KINDF: {
      return f4;
    }
    case ItemKind::e_KINDG: {
      return f5;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 ItemKind_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                         const T1 f3, const T1 f4, const T1 f5,
                         const ItemKind i) {
    switch (i) {
    case ItemKind::e_KINDA: {
      return f;
    }
    case ItemKind::e_KINDB: {
      return f0;
    }
    case ItemKind::e_KINDC: {
      return f1;
    }
    case ItemKind::e_KINDD: {
      return f2;
    }
    case ItemKind::e_KINDE: {
      return f3;
    }
    case ItemKind::e_KINDF: {
      return f4;
    }
    case ItemKind::e_KINDG: {
      return f5;
    }
    default:
      std::unreachable();
    }
  }

  struct StoredTag {
    // TYPES
    struct TagPrimary {
      ItemKind d_a0;
    };

    struct TagSecondary {
      ItemKind d_a0;
    };

    using variant_t = std::variant<TagPrimary, TagSecondary>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    StoredTag() {}

    explicit StoredTag(TagPrimary _v) : d_v_(std::move(_v)) {}

    explicit StoredTag(TagSecondary _v) : d_v_(std::move(_v)) {}

    StoredTag(const StoredTag &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    StoredTag(StoredTag &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) StoredTag &operator=(const StoredTag &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) StoredTag &operator=(StoredTag &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) StoredTag clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<TagPrimary>(_sv.v())) {
        const auto &[d_a0] = std::get<TagPrimary>(_sv.v());
        return StoredTag(TagPrimary{d_a0});
      } else {
        const auto &[d_a0] = std::get<TagSecondary>(_sv.v());
        return StoredTag(TagSecondary{d_a0});
      }
    }

    // CREATORS
    constexpr static StoredTag tagprimary(ItemKind a0) {
      return StoredTag(TagPrimary{std::move(a0)});
    }

    constexpr static StoredTag tagsecondary(ItemKind a0) {
      return StoredTag(TagSecondary{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) StoredTag *operator->() { return this; }

    __attribute__((pure)) const StoredTag *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = StoredTag(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, ItemKind> F0, MapsTo<T1, ItemKind> F1>
  static T1 StoredTag_rect(F0 &&f, F1 &&f0, const StoredTag &s) {
    if (std::holds_alternative<typename StoredTag::TagPrimary>(s.v())) {
      const auto &[d_a0] = std::get<typename StoredTag::TagPrimary>(s.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename StoredTag::TagSecondary>(s.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, ItemKind> F0, MapsTo<T1, ItemKind> F1>
  static T1 StoredTag_rec(F0 &&f, F1 &&f0, const StoredTag &s) {
    if (std::holds_alternative<typename StoredTag::TagPrimary>(s.v())) {
      const auto &[d_a0] = std::get<typename StoredTag::TagPrimary>(s.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename StoredTag::TagSecondary>(s.v());
      return f0(d_a0);
    }
  }
  enum class TraceBucket { e_BUCKETA, e_BUCKETB, e_BUCKETC };

  template <typename T1>
  static T1 TraceBucket_rect(const T1 f, const T1 f0, const T1 f1,
                             const TraceBucket t) {
    switch (t) {
    case TraceBucket::e_BUCKETA: {
      return f;
    }
    case TraceBucket::e_BUCKETB: {
      return f0;
    }
    case TraceBucket::e_BUCKETC: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 TraceBucket_rec(const T1 f, const T1 f0, const T1 f1,
                            const TraceBucket t) {
    switch (t) {
    case TraceBucket::e_BUCKETA: {
      return f;
    }
    case TraceBucket::e_BUCKETB: {
      return f0;
    }
    case TraceBucket::e_BUCKETC: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  struct PrimaryRecord {
    ItemKind primary_left_kind;
    ItemKind primary_right_kind;
    StoredTag primary_tag;

    __attribute__((pure)) PrimaryRecord *operator->() { return this; }

    __attribute__((pure)) const PrimaryRecord *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) PrimaryRecord clone() const {
      return PrimaryRecord{(*(this)).primary_left_kind,
                           (*(this)).primary_right_kind,
                           (*(this)).primary_tag.clone()};
    }
  };

  struct ErasedProofRecord {
    TraceBucket erased_bucket;

    __attribute__((pure)) ErasedProofRecord *operator->() { return this; }

    __attribute__((pure)) const ErasedProofRecord *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) ErasedProofRecord clone() const {
      return ErasedProofRecord{(*(this)).erased_bucket};
    }
  };

  __attribute__((pure)) static unsigned int kind_code(const ItemKind k);
  __attribute__((pure)) static unsigned int tag_code(const StoredTag &t);
  __attribute__((pure)) static unsigned int bucket_code(const TraceBucket b);
  __attribute__((pure)) static StoredTag bucket_to_tag(const TraceBucket b);
  static inline const PrimaryRecord sample_primary_record =
      PrimaryRecord{ItemKind::e_KINDC, ItemKind::e_KINDE,
                    StoredTag::tagprimary(ItemKind::e_KINDC)};
  static inline const ErasedProofRecord sample_erased_proof_record =
      ErasedProofRecord{TraceBucket::e_BUCKETC};
  __attribute__((pure)) static unsigned int
  left_kind_code_of(const PrimaryRecord &r);
  __attribute__((pure)) static unsigned int
  right_kind_code_of(const PrimaryRecord &r);
  __attribute__((pure)) static unsigned int tag_code_of(const PrimaryRecord &r);
  __attribute__((pure)) static unsigned int
  bucket_code_of(const ErasedProofRecord &r);
  __attribute__((pure)) static List<unsigned int>
  trace_codes_of(const PrimaryRecord &primary, const ErasedProofRecord &erased);
  __attribute__((pure)) static unsigned int
  trace_checksum_of(const PrimaryRecord &primary,
                    const ErasedProofRecord &erased);
  static inline const unsigned int sample_left_kind_code =
      left_kind_code_of(sample_primary_record);
  static inline const unsigned int sample_right_kind_code =
      right_kind_code_of(sample_primary_record);
  static inline const unsigned int sample_tag_code =
      tag_code_of(sample_primary_record);
  static inline const unsigned int sample_bucket_code =
      bucket_code_of(sample_erased_proof_record);
  static inline const unsigned int sample_trace_checksum =
      trace_checksum_of(sample_primary_record, sample_erased_proof_record);
};

#endif // INCLUDED_RECORD_ERASED_PROOF_FIELDS
