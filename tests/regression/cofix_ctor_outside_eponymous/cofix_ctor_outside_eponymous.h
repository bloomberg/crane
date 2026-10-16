#ifndef INCLUDED_COFIX_CTOR_OUTSIDE_EPONYMOUS
#define INCLUDED_COFIX_CTOR_OUTSIDE_EPONYMOUS

#include "fn.h"
#include "lazy.h"
#include <cstdint>
#include <utility>
#include <variant>

struct CofixCtorOutsideEponymous {
  struct Stream {
    struct stream {
      // TYPES
      template <typename CraneS0 = stream> struct Scons_ {
        uint64_t a0;
        CraneS0 a1;
      };

      using Scons = Scons_<>;
      using variant_t = std::variant<Scons>;

    private:
      // DATA
      crane::lazy<variant_t> lazy_v_;

    public:
      // CREATORS
      stream() {}

      explicit stream(Scons _v)
          : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

      explicit stream(crane::fn<variant_t()> _thunk)
          : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

      static stream scons(uint64_t a0, stream a1) {
        return stream(crane::lazy<variant_t>(
            std::in_place, std::in_place_index<0>, a0, std::move(a1)));
      }

      explicit stream(crane::lazy<variant_t> _cell)
          : lazy_v_(std::move(_cell)) {}

      template <typename F> static stream lazy_(F &&thunk) {
        return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
      }

      // ACCESSORS
      const variant_t &v() const { return lazy_v_.force(); }

      const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }

      const uint64_t &hd() const & {
        const auto &[a0, a1] = std::get<typename stream::Scons>(this->v());
        return a0;
      }

      uint64_t hd() const && {
        const auto &[a0, a1] = std::get<typename stream::Scons>(this->v());
        return a0;
      }

      const stream &tl() const & {
        const auto &[a0, a1] = std::get<typename stream::Scons>(this->v());
        return a1;
      }

      stream tl() const && {
        const auto &[a0, a1] = std::get<typename stream::Scons>(this->v());
        return a1;
      }
    };
  };

  static Stream::stream from(uint64_t n);
  static uint64_t third_of(uint64_t n);
};

#endif // INCLUDED_COFIX_CTOR_OUTSIDE_EPONYMOUS
