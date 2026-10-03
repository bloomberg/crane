#ifndef INCLUDED_RUNTIME_BLOCK_INVARIANTS
#define INCLUDED_RUNTIME_BLOCK_INVARIANTS

#include "fn.h"
#include "lazy.h"
#include <utility>
#include <variant>

struct RuntimeBlockInvariants {
  struct stream {
    // TYPES
    template <typename _S0 = stream> struct SCons_ {
      uint64_t a0;
      _S0 a1;
    };

    using SCons = SCons_<>;
    using variant_t = std::variant<SCons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    stream() {}

    explicit stream(SCons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream scons(uint64_t a0, stream a1) {
      return stream(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, a0, std::move(a1)));
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream lazy_(F &&thunk) {
      return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static stream from(uint64_t n);
  static uint64_t hd(stream s);
};

#endif // INCLUDED_RUNTIME_BLOCK_INVARIANTS
