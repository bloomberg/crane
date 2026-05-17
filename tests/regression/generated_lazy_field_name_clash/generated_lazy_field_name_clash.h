#ifndef INCLUDED_GENERATED_LAZY_FIELD_NAME_CLASH
#define INCLUDED_GENERATED_LAZY_FIELD_NAME_CLASH

#include "lazy.h"
#include <functional>
#include <memory>
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
    struct Cons {
      bool a0;
      std::shared_ptr<d_lazyV_> a1;
    };

    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit d_lazyV_(Cons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit d_lazyV_(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static d_lazyV_ cons(bool a0, const d_lazyV_ &a1) {
      return d_lazyV_(Cons{a0, std::make_shared<d_lazyV_>(a1)});
    }

    static d_lazyV_ lazy_(std::function<d_lazyV_()> thunk) {
      return d_lazyV_(std::function<variant_t()>([=]() mutable -> variant_t {
        d_lazyV_ _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  static d_lazyV_ true_stream();
  static bool head(d_lazyV_ s);
  static inline const bool sample = head(true_stream());
};

#endif // INCLUDED_GENERATED_LAZY_FIELD_NAME_CLASH
