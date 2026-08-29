#ifndef INCLUDED_NESTEDTYPESCOPE
#define INCLUDED_NESTEDTYPESCOPE

#include <concepts>
#include <utility>

#include "Datatypes.h"

namespace NestedTypeScope {

template <typename M>
concept HasTag = requires {
  typename M::Tag;
  requires(
      requires {
        { M::defTag } -> std::convertible_to<typename M::Tag>;
      } ||
      requires {
        { M::defTag() } -> std::convertible_to<typename M::Tag>;
      });
};

template <HasTag T> struct RuleMod {
  using Rule = typename Datatypes::template Prod<typename T::Tag,
                                                 typename Datatypes::Nat>;
};

struct Tags {
  enum class Tag_ { FOO, BAR, BAZ };

  template <typename T1> static T1 Tag__rect(T1 f, T1 f0, T1 f1, Tag_ t) {
    switch (t) {
    case Tag_::FOO: {
      return f;
    }
    case Tag_::BAR: {
      return f0;
    }
    case Tag_::BAZ: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 Tag__rec(T1 f, T1 f0, T1 f1, Tag_ t) {
    switch (t) {
    case Tag_::FOO: {
      return f;
    }
    case Tag_::BAR: {
      return f0;
    }
    case Tag_::BAZ: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  using Tag = Tag_;

  static const Tag &defTag() {
    static const Tag v = Tag_::FOO;
    return v;
  }
};

using RM = RuleMod<Tags>;
const RM::Rule my_rule =
    Datatypes::template Prod<Tags::Tag_, Datatypes::Nat>::pair(
        Tags::Tag_::BAR,
        Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
            Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                    Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                        Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                            Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                Datatypes::Nat::
                                    s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                        Datatypes::Nat::
                                            s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                                Datatypes::Nat::
                                                    s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                                        Datatypes::Nat::
                                                            s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                                                Datatypes::Nat::
                                                                    s(Datatypes::Nat::s(Datatypes::Nat::s(
                                                                        Datatypes::Nat::
                                                                            o())))))))))))))))))))))))))))))))))))))))))));
const RM::Rule my_rule2 =
    Datatypes::template Prod<Tags::Tag_, Datatypes::Nat>::pair(
        Tags::Tag_::BAZ,
        Datatypes::Nat::s(Datatypes::Nat::s(
            Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::o()))))))));
Tags::Tag get_tag(RM::Rule _x0);
const Tags::Tag test_tag = get_tag(my_rule);

} // namespace NestedTypeScope

#endif // INCLUDED_NESTEDTYPESCOPE
