#ifndef INCLUDED_GENERATED_STORAGE_FIELD_NAME_CLASH
#define INCLUDED_GENERATED_STORAGE_FIELD_NAME_CLASH

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct GeneratedStorageFieldNameClash {
  /// Generated ADT classes store their backing variant in a private field named
  /// d_v_.  If the Rocq inductive itself is named d_v_, Crane generates a
  /// C++ class d_v_ with a data member also named d_v_.  C++ rejects a
  /// non-static data member with the same name as its class, so the generated
  /// code does not compile.
  struct d_v_ {
    // TYPES
    struct Empty {};

    struct Flag {
      bool d_a0;
    };

    using variant_t = std::variant<Empty, Flag>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    d_v_() {}

    explicit d_v_(Empty _v) : d_v_(_v) {}

    explicit d_v_(Flag _v) : d_v_(std::move(_v)) {}

    d_v_(const d_v_ &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    d_v_(d_v_ &&_other) : d_v_(std::move(_other.d_v_)) {}

    d_v_ &operator=(const d_v_ &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    d_v_ &operator=(d_v_ &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    d_v_ clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Empty>(_sv.v())) {
        return d_v_(Empty{});
      } else {
        const auto &[d_a0] = std::get<Flag>(_sv.v());
        return d_v_(Flag{d_a0});
      }
    }

    // CREATORS
    static d_v_ empty() { return d_v_(Empty{}); }

    static d_v_ flag(bool a0) { return d_v_(Flag{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, bool> F1>
  static T1 d_v__rect(const T1 f, F1 &&f0, const d_v_ &d) {
    if (std::holds_alternative<typename d_v_::Empty>(d.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename d_v_::Flag>(d.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, bool> F1>
  static T1 d_v__rec(const T1 f, F1 &&f0, const d_v_ &d) {
    if (std::holds_alternative<typename d_v_::Empty>(d.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename d_v_::Flag>(d.v());
      return f0(d_a0);
    }
  }

  static bool is_flag(const d_v_ &x);
  static inline const bool sample = is_flag(d_v_::flag(true));
};

#endif // INCLUDED_GENERATED_STORAGE_FIELD_NAME_CLASH
