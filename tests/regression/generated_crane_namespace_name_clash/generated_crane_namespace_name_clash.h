#ifndef INCLUDED_GENERATED_CRANE_NAMESPACE_NAME_CLASH
#define INCLUDED_GENERATED_CRANE_NAMESPACE_NAME_CLASH

#include "lazy.h"
#include <functional>
#include <memory>
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
    struct Cons {
      bool d_a0;
      std::shared_ptr<stream> d_a1;
    };

    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit stream(Cons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream cons(bool a0, const stream &a1) {
      return stream(Cons{a0, std::make_shared<stream>(a1)});
    }

    static stream lazy_(std::function<stream()> thunk) {
      return stream(std::function<variant_t()>([=]() mutable -> variant_t {
        stream _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return d_lazyV_.force(); }
  };

  static stream ones();
  static bool head(stream s);
  static inline const bool sample = head(ones());
};

#endif // INCLUDED_GENERATED_CRANE_NAMESPACE_NAME_CLASH
