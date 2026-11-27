#pragma once

#include <cstdint>
#include <type_traits>
#include <utility>

#include "Datatypes.h"
#include "ListDef.h"

namespace Lib {
template <typename M>
concept L = requires {
  typename M::Label;
};

template <L X> struct DefsFn {
  using Token = std::pair<typename X::Label, uint64_t>;
};

template <L X> struct LexFn {
  using D = DefsFn<X>;

  static std::pair<typename Datatypes::template List<typename D::Token>,
                   typename Datatypes::template List<uint64_t>>
  lex(const typename Datatypes::template List<typename X::Label> &rus,
      const typename Datatypes::template List<uint64_t> &code) {
    return std::make_pair(
        ListDef::template map<typename X::Label,
                              std::pair<typename X::Label, uint64_t>>(
            [=, code = code](typename X::Label r) {
              return std::make_pair(std::move(r), code.length());
            },
            rus),
        code);
  }
};

template <L X, typename LX> struct SemFn {
  template <typename F0>
    requires std::is_invocable_r_v<
      std::pair<typename Datatypes::template List<
          std::pair<typename X::Label, uint64_t>>,
                typename Datatypes::template List<uint64_t>>,
      F0 &, const typename Datatypes::template List<uint64_t> &>
  static uint64_t
  lex_with(F0 &&lx, const typename Datatypes::template List<uint64_t> &code) {
    return lx(code).first.length();
  }
};
} // namespace Lib
