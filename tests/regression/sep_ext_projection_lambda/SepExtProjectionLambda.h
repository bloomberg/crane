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
    uint64_t label;
    typename S::A payload;

    // ACCESSORS
    item clone() const { return item{this->label, this->payload}; }
  };

  static uint64_t get_label(const item &x) { return x.label; }

  static typename Datatypes::template List<uint64_t>
  all_labels(const typename Datatypes::template List<item> &xs) {
    return xs.template map<uint64_t>([](const item &i) { return i.label; });
  }

  static std::optional<typename S::A>
  find_label(uint64_t target,
             const typename Datatypes::template List<item> &xs) {
    if (std::holds_alternative<typename Datatypes::template List<item>::Nil>(
            xs.v())) {
      return std::optional<typename S::A>();
    } else {
      const auto &[a0, a1] =
          std::get<typename Datatypes::template List<item>::Cons>(xs.v());
      if (a0.label == target) {
        return std::make_optional<typename S::A>(a0.payload);
      } else {
        return find_label(target, *a1);
      }
    }
  }
};

} // namespace SepExtProjectionLambda

#endif // INCLUDED_SEPEXTPROJECTIONLAMBDA
