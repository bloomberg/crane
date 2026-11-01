#ifndef INCLUDED_FUNCTOR_PARAM_CTOR_FIELD
#define INCLUDED_FUNCTOR_PARAM_CTOR_FIELD

#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// A constructor field whose type is a custom applied to a functor's
/// parameter type: lhs : option nt, option a custom, its inductive
/// declared in the parameter's signature.  Extraction carried the type
/// argument nt among the custom's term arguments too, and the field's
/// conversion read it as a value -- a callee no callable plan exists for.
/// From ParseALot's SllOptimizationSound.
template <typename M>
concept T = requires {
  typename M::nt;
  typename M::frame;
};

struct FunctorParamCtorField {
  template <T D> struct Impl {
    static typename D::frame mk(typename D::nt x) {
      return D::frame::fr(std::make_optional<typename D::nt>(std::move(x)),
                          UINT64_C(0));
    }

    static uint64_t depth(const typename D::frame &f) {
      const auto &[lhs, n0] = f;
      return n0;
    }
  };

  struct Names {
    using nt = bool;

    struct frame {
      // DATA
      std::optional<nt> lhs;
      uint64_t n;

      // ACCESSORS
      frame clone() const { return {lhs, n}; }

      // CREATORS
      static frame fr(std::optional<nt> lhs, uint64_t n) {
        return {std::move(lhs), n};
      }
    };

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const std::optional<bool> &,
                                     const uint64_t &>
    static T1 frame_rect(F0 &&f, const frame &f0) {
      const auto &[lhs0, n0] = f0;
      return f(lhs0, n0);
    }

    template <typename T1, typename F0>
    static T1 frame_rec(F0 &&f, const frame &f0) {
      return frame_rect<T1>(f, f0);
    }
  };

  using NamesImpl = Impl<Names>;
  static uint64_t made_depth(bool b);
};

#endif // INCLUDED_FUNCTOR_PARAM_CTOR_FIELD
