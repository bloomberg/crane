#ifndef INCLUDED_RECORD_APPLY
#define INCLUDED_RECORD_APPLY

#include <functional>

struct RecordApply {
  struct R {
    std::function<unsigned int(unsigned int, unsigned int)> f;
    unsigned int _tag;

    // ACCESSORS
    R clone() const { return R{(*this).f, (*this)._tag}; }
  };

  static unsigned int apply_record(const R &r0, unsigned int a, unsigned int b);
  static inline const R r =
      R{[](unsigned int x, unsigned int) { return x; }, 3u};
  static inline const unsigned int three = r.f(3u, 0u);
};

#endif // INCLUDED_RECORD_APPLY
