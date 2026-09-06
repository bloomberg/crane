#ifndef INCLUDED_MODTYPE_LOCAL_TYPE_REF
#define INCLUDED_MODTYPE_LOCAL_TYPE_REF

#include <concepts>
#include <utility>

template <typename M>
concept STORE = requires {
  {
    M::lookup(std::declval<ModtypeLocalTypeRef::entry>(),
              std::declval<ModtypeLocalTypeRef::key>())
  } -> std::same_as<uint64_t>;
};
template <typename M>
concept SHIFT = requires {
  {
    M::shift(std::declval<ModtypeLocalTypeRef::point>(),
             std::declval<uint64_t>())
  } -> std::same_as<ModtypeLocalTypeRef::point>;
};

struct ModtypeLocalTypeRef {
  using key = uint64_t;
  using entry = std::pair<key, uint64_t>;

  struct point {
    uint64_t px;
    uint64_t py;
  };

  struct S {
    static uint64_t lookup(const std::pair<uint64_t, uint64_t> &e, uint64_t k);
  };

  static_assert(STORE<S>);

  struct T {
    static point shift(const point &p, uint64_t d);
  };

  static_assert(SHIFT<T>);
  static inline const uint64_t run =
      (S::lookup(std::make_pair(UINT64_C(1), UINT64_C(42)), UINT64_C(1)) +
       T::shift(point{UINT64_C(1), UINT64_C(2)}, UINT64_C(3)).px);
};

#endif // INCLUDED_MODTYPE_LOCAL_TYPE_REF
