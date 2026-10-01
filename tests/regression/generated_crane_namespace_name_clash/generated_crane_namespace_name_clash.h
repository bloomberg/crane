#ifndef INCLUDED_GENERATED_CRANE_NAMESPACE_NAME_CLASH
#define INCLUDED_GENERATED_CRANE_NAMESPACE_NAME_CLASH

#include "fn.h"
#include "lazy.h"
#include <utility>
#include <variant>

struct crane_ {
  /// Coinductive extraction includes lazy.h, which declares namespace crane.
  /// If the extracted Rocq module is also named crane, Crane emits a global
  /// C++ struct crane in the same namespace scope.  The generated C++ does not
  /// compile because a namespace and a struct cannot share the same global
  /// name.
  struct stream {
    // TYPES
    template <typename _S0 = stream> struct Cons_ {
      bool a0;
      _S0 a1;
    };

    using Cons = Cons_<>;
    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    stream() {}

    explicit stream(Cons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream cons(bool a0, stream a1) {
      return stream(Cons{a0, std::move(a1)});
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream lazy_(F &&thunk) {
      return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static stream ones();
  static bool head(stream s);
  static inline const bool sample = head(ones());
};

#endif // INCLUDED_GENERATED_CRANE_NAMESPACE_NAME_CLASH
