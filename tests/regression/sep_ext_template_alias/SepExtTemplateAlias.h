#ifndef INCLUDED_SEPEXTTEMPLATEALIAS
#define INCLUDED_SEPEXTTEMPLATEALIAS

namespace SepExtTemplateAlias {

template <typename M>
concept OT = requires { typename M::t; };

template <OT X> struct WFacts_fun {
  using foo = typename X::t;
};

template <OT X> using WFacts = WFacts_fun<X>;

} // namespace SepExtTemplateAlias

#endif // INCLUDED_SEPEXTTEMPLATEALIAS
