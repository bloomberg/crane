#ifndef INCLUDED_REUSE_TAG_MISMATCH
#define INCLUDED_REUSE_TAG_MISMATCH

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ReuseTagMismatch {
  /// BUG HYPOTHESIS: The reuse optimization mutates variant fields in-place
  /// when use_count() == 1 and the tail constructor has the same arity
  /// as the matched constructor, even when they are DIFFERENT constructors.
  /// This leaves the variant with the WRONG tag — the original matched
  /// constructor tag persists instead of changing to the tail constructor.
  ///
  /// The reuse optimization fires when:
  /// 1. The scrutinee is "owned" (escapes in some code path)
  /// 2. The tail constructor has the same arity as the matched constructor
  /// 3. same_inductive holds (same type)
  /// 4. use_count() == 1 at runtime
  ///
  /// It does NOT check that matched_ctor == tail_ctor.
  struct direction {
    // TYPES
    struct GoUp {
      unsigned int d_a0;
    };

    struct GoDown {
      unsigned int d_a0;
    };

    using variant_t = std::variant<GoUp, GoDown>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit direction(GoUp _v) : d_v_(std::move(_v)) {}

    explicit direction(GoDown _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<direction> goup(unsigned int a0) {
      return std::make_shared<direction>(GoUp{std::move(a0)});
    }

    static std::shared_ptr<direction> godown(unsigned int a0) {
      return std::make_shared<direction>(GoDown{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 direction_rect(F0 &&f, F1 &&f0,
                           const std::shared_ptr<direction> &d) {
    if (std::holds_alternative<typename direction::GoUp>(d->v())) {
      const auto &[d_a0] = std::get<typename direction::GoUp>(d->v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename direction::GoDown>(d->v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 direction_rec(F0 &&f, F1 &&f0,
                          const std::shared_ptr<direction> &d) {
    if (std::holds_alternative<typename direction::GoUp>(d->v())) {
      const auto &[d_a0] = std::get<typename direction::GoUp>(d->v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename direction::GoDown>(d->v());
      return f0(d_a0);
    }
  }

  /// The 'else d' branch causes d to escape (returned in tail position).
  /// This makes d "owned" (infer_owned_params marks it).
  /// The 'then' branch's match has reuse candidates because:
  /// - GoUp/GoDown are the same inductive (direction)
  /// - Both have arity 1
  /// But GoUp and GoDown are DIFFERENT constructors.
  static std::shared_ptr<direction> id_or_flip(std::shared_ptr<direction> d,
                                               const bool flip_flag);
  /// test1: flip GoUp 42 -> should be GoDown 42.
  /// Match on the result:
  /// - GoUp _ => 1 (wrong, reuse bug would make this match)
  /// - GoDown _ => 2 (correct)
  static inline const unsigned int test1 = []() {
    auto &&_sv = id_or_flip(direction::goup(42u), true);
    if (std::holds_alternative<typename direction::GoUp>(_sv->v())) {
      return 1u;
    } else {
      return 2u;
    }
  }();
  /// test2: no flip -> should be GoUp 42 unchanged.
  static inline const unsigned int test2 = []() {
    auto &&_sv = id_or_flip(direction::goup(42u), false);
    if (std::holds_alternative<typename direction::GoUp>(_sv->v())) {
      return 1u;
    } else {
      return 2u;
    }
  }();
  /// test3: flip GoDown 100 -> should be GoUp 100.
  static inline const unsigned int test3 = []() {
    auto &&_sv = id_or_flip(direction::godown(100u), true);
    if (std::holds_alternative<typename direction::GoUp>(_sv->v())) {
      return 3u;
    } else {
      return 4u;
    }
  }();
  /// test4: use the flipped value's payload.
  static inline const unsigned int test4 = []() {
    auto &&_sv3 = id_or_flip(direction::goup(10u), true);
    if (std::holds_alternative<typename direction::GoUp>(_sv3->v())) {
      const auto &[d_a03] = std::get<typename direction::GoUp>(_sv3->v());
      return (d_a03 + 1000u);
    } else {
      const auto &[d_a03] = std::get<typename direction::GoDown>(_sv3->v());
      return d_a03;
    }
  }();
};

#endif // INCLUDED_REUSE_TAG_MISMATCH
