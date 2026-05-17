#ifndef INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE
#define INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE

#include <any>
#include <utility>
#include <variant>

enum class Bool0 { TRUE_, FALSE_ };

struct TypeIndexedInductiveProbe {
  /// Regression test for type-indexed inductives with erased type parameters.
  ///
  /// Inductive wrap is indexed by a Set; the type parameter A is erased
  /// in C++, so the field d_a is typed std::any.  When matching w : wrap
  /// bool at the concrete index bool, the branch body b must be recovered
  /// via std::any_cast<Bool0>.  Previously Crane emitted a bare return d_a
  /// instead, causing a compile error:
  /// error: no viable conversion from 'std::any' to 'const Bool0'
  struct wrap {
    // TYPES
    struct Wrap0 {
      std::any a;
    };

    using variant_t = std::variant<Wrap0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    wrap() {}

    explicit wrap(Wrap0 _v) : v_(std::move(_v)) {}

    wrap(const wrap &_other) : v_(std::move(_other.clone().v_)) {}

    wrap(wrap &&_other) : v_(std::move(_other.v_)) {}

    wrap &operator=(const wrap &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    wrap &operator=(wrap &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    wrap clone() const {
      const auto &[a] = std::get<Wrap0>(this->v());
      return wrap(Wrap0{a});
    }

    // CREATORS
    static wrap wrap0(std::any a) { return wrap(Wrap0{std::move(a)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0>
  static T1 wrap_rect(F0 &&f, const wrap &w0) {
    const auto &[a0] = std::get<typename wrap::Wrap0>(w0.v());
    return std::any_cast<T1>(f(std::any_cast<T2>(a0)));
  }

  template <typename T1, typename T2, typename F0>
  static T1 wrap_rec(F0 &&f, const wrap &w0) {
    const auto &[a0] = std::get<typename wrap::Wrap0>(w0.v());
    return std::any_cast<T1>(f(std::any_cast<T2>(a0)));
  }

  static inline const wrap w = wrap::wrap0(Bool0::TRUE_);
  static inline const Bool0 sample = []() {
    auto &&_sv0 = w;
    const auto &[a0] = std::get<typename wrap::Wrap0>(_sv0.v());
    return std::any_cast<Bool0>(a0);
  }();
};

#endif // INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE
