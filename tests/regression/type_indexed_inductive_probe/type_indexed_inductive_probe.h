#ifndef INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE
#define INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

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
      std::any d_a;
    };

    using variant_t = std::variant<Wrap0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit wrap(Wrap0 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<wrap> wrap0(std::any a) {
      return std::make_shared<wrap>(Wrap0{std::move(a)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F0>
  static T1 wrap_rect(F0 &&f, const std::shared_ptr<wrap> &w0) {
    const auto &[d_a] = std::get<typename wrap::Wrap0>(w0->v());
    return std::any_cast<T1>(f(d_a));
  }

  template <typename T1, typename F0>
  static T1 wrap_rec(F0 &&f, const std::shared_ptr<wrap> &w0) {
    const auto &[d_a] = std::get<typename wrap::Wrap0>(w0->v());
    return std::any_cast<T1>(f(d_a));
  }

  static inline const std::shared_ptr<wrap> w = wrap::wrap0(Bool0::e_TRUE0);
  static inline const Bool0 sample = []() {
    auto &&_sv0 = w;
    const auto &[d_a0] = std::get<typename wrap::Wrap0>(_sv0->v());
    return std::any_cast<Bool0>(d_a0);
  }();
};

#endif // INCLUDED_TYPE_INDEXED_INDUCTIVE_PROBE
