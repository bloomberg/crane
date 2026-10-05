#ifndef INCLUDED_RECORD_ERASED_PROOF_FIELDS
#define INCLUDED_RECORD_ERASED_PROOF_FIELDS

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
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
  static T1 ItemKind_rec(const T1 &f, const T1 &f0, const T1 &f1, const T1 &f2,
                         const T1 &f3, const T1 &f4, const T1 &f5, ItemKind i) {
    return ItemKind_rect<T1>(f, f0, f1, f2, f3, f4, f5, i);
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
    requires std::is_invocable_r_v<T1, F0 &, const ItemKind &> &&
             std::is_invocable_r_v<T1, F1 &, const ItemKind &>
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
  static T1 StoredTag_rec(F0 &&f, F1 &&f0, const StoredTag &s) {
    return StoredTag_rect<T1>(f, f0, s);
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
  static T1 TraceBucket_rec(const T1 &f, const T1 &f0, const T1 &f1,
                            TraceBucket t) {
    return TraceBucket_rect<T1>(f, f0, f1, t);
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
  static constexpr uint64_t sample_left_kind_code = UINT64_C(2);
  static constexpr uint64_t sample_right_kind_code = UINT64_C(4);
  static constexpr uint64_t sample_tag_code = UINT64_C(12);
  static constexpr uint64_t sample_bucket_code = UINT64_C(32);
  static constexpr uint64_t sample_trace_checksum = UINT64_C(71);
};

#endif // INCLUDED_RECORD_ERASED_PROOF_FIELDS
