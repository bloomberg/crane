#ifndef INCLUDED_RECORD_APPLY
#define INCLUDED_RECORD_APPLY

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RecordApply {
  struct R {
    std::function<unsigned int(unsigned int, unsigned int)> f;
    unsigned int _tag;

    __attribute__((pure)) R *operator->() { return this; }

    __attribute__((pure)) const R *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) R clone() const {
      return R{(*(this)).f, (*(this))._tag};
    }
  };

  __attribute__((pure)) static unsigned int
  apply_record(const R &r0, const unsigned int &a, const unsigned int &b);
  static inline const R r =
      R{[](unsigned int x, const unsigned int &) { return x; }, 3u};
  static inline const unsigned int three = r.f(3u, 0u);
};

#endif // INCLUDED_RECORD_APPLY
