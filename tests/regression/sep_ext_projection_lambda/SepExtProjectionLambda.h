#ifndef INCLUDED_SEPEXTPROJECTIONLAMBDA
#define INCLUDED_SEPEXTPROJECTIONLAMBDA

#include <memory>
#include <optional>
#include <variant>

#include "Datatypes.h"
#include "ListDef.h"

namespace SepExtProjectionLambda {

template <typename M>
concept Sig = requires { typename M::A; };

template <Sig S> struct Worker {
  struct item {
    unsigned int label;
    typename S::A payload;

    // ACCESSORS
    item clone() const { return item{(*this).label, (*this).payload}; }
  };

  static unsigned int get_label(const item &x) { return x.label; }

  static typename Datatypes::template List<unsigned int>
  all_labels(const typename Datatypes::template List<item> &xs) {
    return xs.template map<unsigned int>([](const item &i) { return i.label; });
  }

  static std::optional<typename S::A>
  find_label(unsigned int target,
             const typename Datatypes::template List<item> &xs) {
    if (std::holds_alternative<typename Datatypes::template List<item>::Nil>(
            xs.v())) {
      return std::optional<typename S::A>();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename Datatypes::template List<item>::Cons>(xs.v());
      if (d_a0.label == target) {
        return std::make_optional<typename S::A>(d_a0.payload);
      } else {
        return find_label(target, *d_a1);
      }
    }
  }
};

} // namespace SepExtProjectionLambda

#endif // INCLUDED_SEPEXTPROJECTIONLAMBDA
