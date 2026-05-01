#ifndef INCLUDED_GENERATED_CONCEPT_NAME_CLASH
#define INCLUDED_GENERATED_CONCEPT_NAME_CLASH

#include <memory>
#include <optional>
#include <type_traits>

struct MapsTo {
  /// Every generated header currently declares a global C++ concept named
  /// MapsTo.  If the extracted Rocq module is also named MapsTo, Crane emits
  /// both the concept and a struct with the same global C++ name.  The
  /// generated C++ does not compile because the concept name and struct name
  /// collide in the same namespace.
  static inline const bool sample = true;
};

#endif // INCLUDED_GENERATED_CONCEPT_NAME_CLASH
