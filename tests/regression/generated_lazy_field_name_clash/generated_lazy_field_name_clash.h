#ifndef INCLUDED_GENERATED_LAZY_FIELD_NAME_CLASH
#define INCLUDED_GENERATED_LAZY_FIELD_NAME_CLASH

#include "fn.h"
#include "lazy.h"
#include <utility>
#include <variant>

struct GeneratedLazyFieldNameClash {
  /// Generated coinductive classes store their forced value in a lazy field
  /// named d_lazyV_.  If the Rocq coinductive itself is named d_lazyV_, Crane
  /// generates a C++ class d_lazyV_ with a data member also named d_lazyV_.
  /// This hides the class name inside its own scope and breaks constructors and
  /// method signatures, so the generated C++ does not compile.
  struct d_lazyV_ {
    // TYPES
    template <typename CraneS0 = d_lazyV_> struct Cons_ {
      bool a0;
      CraneS0 a1;
    };

    using Cons = Cons_<>;
    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    d_lazyV_() {}

    explicit d_lazyV_(Cons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit d_lazyV_(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static d_lazyV_ cons(bool a0, d_lazyV_ a1) {
      return d_lazyV_(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, a0, std::move(a1)));
    }

    explicit d_lazyV_(crane::lazy<variant_t> _cell)
        : lazy_v_(std::move(_cell)) {}

    template <typename F> static d_lazyV_ lazy_(F &&thunk) {
      return d_lazyV_(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static d_lazyV_ true_stream();
  static bool head(d_lazyV_ s);
  static inline const bool sample = head(true_stream());
};

#endif // INCLUDED_GENERATED_LAZY_FIELD_NAME_CLASH
