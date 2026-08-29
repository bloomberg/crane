#ifndef INCLUDED_ASSOC_TYPE_ANY_CAST
#define INCLUDED_ASSOC_TYPE_ANY_CAST

#include <any>
#include <concepts>
#include <utility>

/// A type class with an associated Type field.  The instance's method
/// parameter is correctly specialised to std::pair<uint64_t, uint64_t>,
/// but its body still any_casts the parameter as if it were erased, so the
/// generated instance does not compile.
template <typename I>
concept Wrap = requires {
  typename I::W;
  { I::wrap(std::declval<uint64_t>()) } -> std::convertible_to<typename I::W>;
  { I::unwrap(std::declval<typename I::W>()) } -> std::convertible_to<uint64_t>;
};

struct AssocTypeAnyCast {
  using W = std::any;

  struct PairWrap {
    using W = std::pair<uint64_t, uint64_t>;

    static std::pair<uint64_t, uint64_t> wrap(uint64_t n) {
      return std::make_pair(n, n);
    }

    static uint64_t unwrap(std::pair<uint64_t, uint64_t> p) {
      return (p.first + p.second);
    }
  };

  static_assert(Wrap<PairWrap>);

  template <Wrap _tcI0> static uint64_t roundtrip(uint64_t n) {
    return _tcI0::unwrap(_tcI0::wrap(n));
  }

  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_ASSOC_TYPE_ANY_CAST
