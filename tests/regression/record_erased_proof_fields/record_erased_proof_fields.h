#ifndef INCLUDED_RECORD_ERASED_PROOF_FIELDS
#define INCLUDED_RECORD_ERASED_PROOF_FIELDS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{
            [&](const typename List<t_A>::Nil _args) -> T1 { return a0; },
            [&](const typename List<t_A>::Cons _args) -> T1 {
              return _args.d_a1->template fold_left<T1>(f, f(a0, _args.d_a0));
            }},
        this->v());
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
    return [&](void) {
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
      }
    }();
  }

  template <typename T1>
  static T1 ItemKind_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                         const T1 f3, const T1 f4, const T1 f5,
                         const ItemKind i) {
    return [&](void) {
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
      }
    }();
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
    explicit StoredTag(TagPrimary _v) : d_v_(std::move(_v)) {}

    explicit StoredTag(TagSecondary _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<StoredTag> tagprimary(ItemKind a0) {
      return std::make_shared<StoredTag>(TagPrimary{std::move(a0)});
    }

    static std::shared_ptr<StoredTag> tagsecondary(ItemKind a0) {
      return std::make_shared<StoredTag>(TagSecondary{std::move(a0)});
    }

    static std::unique_ptr<StoredTag> tagprimary_uptr(ItemKind a0) {
      return std::make_unique<StoredTag>(TagPrimary{std::move(a0)});
    }

    static std::unique_ptr<StoredTag> tagsecondary_uptr(ItemKind a0) {
      return std::make_unique<StoredTag>(TagSecondary{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, ItemKind> F0, MapsTo<T1, ItemKind> F1>
  static T1 StoredTag_rect(F0 &&f, F1 &&f0,
                           const std::shared_ptr<StoredTag> &s) {
    return std::visit(
        Overloaded{[&](const typename StoredTag::TagPrimary _args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename StoredTag::TagSecondary _args) -> T1 {
                     return f0(_args.d_a0);
                   }},
        s->v());
  }

  template <typename T1, MapsTo<T1, ItemKind> F0, MapsTo<T1, ItemKind> F1>
  static T1 StoredTag_rec(F0 &&f, F1 &&f0,
                          const std::shared_ptr<StoredTag> &s) {
    return std::visit(
        Overloaded{[&](const typename StoredTag::TagPrimary _args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename StoredTag::TagSecondary _args) -> T1 {
                     return f0(_args.d_a0);
                   }},
        s->v());
  }
  enum class TraceBucket { e_BUCKETA, e_BUCKETB, e_BUCKETC };

  template <typename T1>
  static T1 TraceBucket_rect(const T1 f, const T1 f0, const T1 f1,
                             const TraceBucket t) {
    return [&](void) {
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
      }
    }();
  }

  template <typename T1>
  static T1 TraceBucket_rec(const T1 f, const T1 f0, const T1 f1,
                            const TraceBucket t) {
    return [&](void) {
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
      }
    }();
  }

  struct PrimaryRecord {
    ItemKind primary_left_kind;
    ItemKind primary_right_kind;
    std::shared_ptr<StoredTag> primary_tag;
  };

  struct ErasedProofRecord {
    TraceBucket erased_bucket;
  };

  __attribute__((pure)) static unsigned int kind_code(const ItemKind k);
  __attribute__((pure)) static unsigned int
  tag_code(const std::shared_ptr<StoredTag> &t);
  __attribute__((pure)) static unsigned int bucket_code(const TraceBucket b);
  static std::shared_ptr<StoredTag> bucket_to_tag(const TraceBucket b);
  static inline const std::shared_ptr<PrimaryRecord> sample_primary_record =
      std::make_shared<PrimaryRecord>(
          PrimaryRecord{ItemKind::e_KINDC, ItemKind::e_KINDE,
                        StoredTag::tagprimary(ItemKind::e_KINDC)});
  static inline const std::shared_ptr<ErasedProofRecord>
      sample_erased_proof_record = std::make_shared<ErasedProofRecord>(
          ErasedProofRecord{TraceBucket::e_BUCKETC});
  __attribute__((pure)) static unsigned int
  left_kind_code_of(const std::shared_ptr<PrimaryRecord> &r);
  __attribute__((pure)) static unsigned int
  right_kind_code_of(const std::shared_ptr<PrimaryRecord> &r);
  __attribute__((pure)) static unsigned int
  tag_code_of(const std::shared_ptr<PrimaryRecord> &r);
  __attribute__((pure)) static unsigned int
  bucket_code_of(const std::shared_ptr<ErasedProofRecord> &r);
  static std::shared_ptr<List<unsigned int>>
  trace_codes_of(std::shared_ptr<PrimaryRecord> primary,
                 std::shared_ptr<ErasedProofRecord> erased);
  __attribute__((pure)) static unsigned int
  trace_checksum_of(const std::shared_ptr<PrimaryRecord> &primary,
                    const std::shared_ptr<ErasedProofRecord> &erased);
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
