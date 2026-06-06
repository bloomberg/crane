#ifndef INCLUDED_RECORD_ERASED_PROOF_FIELDS
#define INCLUDED_RECORD_ERASED_PROOF_FIELDS

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return a2->template fold_left<T1>(f, f(a0, a1));
    }
  }
};

struct RecordErasedProofFieldsCase {
  enum class ItemKind { KINDA, KINDB, KINDC, KINDD, KINDE, KINDF, KINDG };

  template <typename T1>
  static T1 ItemKind_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5,
                          ItemKind i) {
    switch (i) {
    case ItemKind::KINDA: {
      return f;
    }
    case ItemKind::KINDB: {
      return f0;
    }
    case ItemKind::KINDC: {
      return f1;
    }
    case ItemKind::KINDD: {
      return f2;
    }
    case ItemKind::KINDE: {
      return f3;
    }
    case ItemKind::KINDF: {
      return f4;
    }
    case ItemKind::KINDG: {
      return f5;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 ItemKind_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, T1 f5,
                         ItemKind i) {
    switch (i) {
    case ItemKind::KINDA: {
      return f;
    }
    case ItemKind::KINDB: {
      return f0;
    }
    case ItemKind::KINDC: {
      return f1;
    }
    case ItemKind::KINDD: {
      return f2;
    }
    case ItemKind::KINDE: {
      return f3;
    }
    case ItemKind::KINDF: {
      return f4;
    }
    case ItemKind::KINDG: {
      return f5;
    }
    default:
      std::unreachable();
    }
  }

  struct StoredTag {
    // TYPES
    struct TagPrimary {
      ItemKind a0;
    };

    struct TagSecondary {
      ItemKind a0;
    };

    using variant_t = std::variant<TagPrimary, TagSecondary>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    StoredTag() {}

    explicit StoredTag(TagPrimary _v) : v_(std::move(_v)) {}

    explicit StoredTag(TagSecondary _v) : v_(std::move(_v)) {}

    static StoredTag tagprimary(ItemKind a0) {
      return StoredTag(TagPrimary{a0});
    }

    static StoredTag tagsecondary(ItemKind a0) {
      return StoredTag(TagSecondary{a0});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, ItemKind &> &&
             std::is_invocable_r_v<T1, F1 &, ItemKind &>
  static T1 StoredTag_rect(F0 &&f, F1 &&f0, const StoredTag &s) {
    if (std::holds_alternative<typename StoredTag::TagPrimary>(s.v())) {
      const auto &[a0] = std::get<typename StoredTag::TagPrimary>(s.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename StoredTag::TagSecondary>(s.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, ItemKind &> &&
             std::is_invocable_r_v<T1, F1 &, ItemKind &>
  static T1 StoredTag_rec(F0 &&f, F1 &&f0, const StoredTag &s) {
    if (std::holds_alternative<typename StoredTag::TagPrimary>(s.v())) {
      const auto &[a0] = std::get<typename StoredTag::TagPrimary>(s.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename StoredTag::TagSecondary>(s.v());
      return f0(a0);
    }
  }
  enum class TraceBucket { BUCKETA, BUCKETB, BUCKETC };

  template <typename T1>
  static T1 TraceBucket_rect(T1 f, T1 f0, T1 f1, TraceBucket t) {
    switch (t) {
    case TraceBucket::BUCKETA: {
      return f;
    }
    case TraceBucket::BUCKETB: {
      return f0;
    }
    case TraceBucket::BUCKETC: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 TraceBucket_rec(T1 f, T1 f0, T1 f1, TraceBucket t) {
    switch (t) {
    case TraceBucket::BUCKETA: {
      return f;
    }
    case TraceBucket::BUCKETB: {
      return f0;
    }
    case TraceBucket::BUCKETC: {
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
  };

  struct ErasedProofRecord {
    TraceBucket erased_bucket;
  };

  static uint64_t kind_code(ItemKind k);
  static uint64_t tag_code(const StoredTag &t);
  static uint64_t bucket_code(TraceBucket b);
  static StoredTag bucket_to_tag(TraceBucket b);
  static inline const PrimaryRecord sample_primary_record = PrimaryRecord{
      ItemKind::KINDC, ItemKind::KINDE, StoredTag::tagprimary(ItemKind::KINDC)};
  static inline const ErasedProofRecord sample_erased_proof_record =
      ErasedProofRecord{TraceBucket::BUCKETC};
  static uint64_t left_kind_code_of(const PrimaryRecord &r);
  static uint64_t right_kind_code_of(const PrimaryRecord &r);
  static uint64_t tag_code_of(const PrimaryRecord &r);
  static uint64_t bucket_code_of(const ErasedProofRecord &r);
  static List<uint64_t> trace_codes_of(const PrimaryRecord &primary,
                                       const ErasedProofRecord &erased);
  static uint64_t trace_checksum_of(const PrimaryRecord &primary,
                                    const ErasedProofRecord &erased);
  static inline const uint64_t sample_left_kind_code =
      left_kind_code_of(sample_primary_record);
  static inline const uint64_t sample_right_kind_code =
      right_kind_code_of(sample_primary_record);
  static inline const uint64_t sample_tag_code =
      tag_code_of(sample_primary_record);
  static inline const uint64_t sample_bucket_code =
      bucket_code_of(sample_erased_proof_record);
  static inline const uint64_t sample_trace_checksum =
      trace_checksum_of(sample_primary_record, sample_erased_proof_record);
};

#endif // INCLUDED_RECORD_ERASED_PROOF_FIELDS
