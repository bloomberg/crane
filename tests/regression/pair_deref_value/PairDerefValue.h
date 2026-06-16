#ifndef INCLUDED_PAIRDEREFVALUE
#define INCLUDED_PAIRDEREFVALUE

#include <concepts>
#include <utility>
#include <variant>
#include <vector>

#include "Datatypes.h"

namespace PairDerefValue {

template <typename M>
concept HasKey = requires {
  typename M::key;
  {
    M::key_eq_dec(std::declval<typename M::key>(),
                  std::declval<typename M::key>())
  } -> std::same_as<bool>;
};

template <HasKey K> struct Collector {
  using production =
      std::pair<typename K::key,
                typename Datatypes::template List<typename K::key>>;

  static typename Datatypes::template List<
      typename Datatypes::template List<typename K::key>>
  rhss_for(
      const typename Datatypes::template List<std::pair<
          typename K::key, typename Datatypes::template List<typename K::key>>>
          &ps,
      typename K::key
          x) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const typename Datatypes::template List<std::pair<
          typename K::key, typename Datatypes::template List<typename K::key>>>
          *ps;
    };

    /// _Resume1: saves [gamma], resumes after recursive call with _result.
    struct _Resume1 {
      typename Datatypes::template List<typename K::key> gamma;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    typename Datatypes::template List<
        typename Datatypes::template List<typename K::key>>
        _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&ps});
    /// Loopified rhss_for: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const typename Datatypes::template List<
            std::pair<typename K::key,
                      typename Datatypes::template List<typename K::key>>> &ps =
            *_f.ps;
        if (std::holds_alternative<typename Datatypes::template List<std::pair<
                typename K::key,
                typename Datatypes::template List<typename K::key>>>::Nil>(
                ps.v())) {
          _result = Datatypes::template List<
              typename Datatypes::template List<typename K::key>>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename Datatypes::template List<
              std::pair<typename K::key, typename Datatypes::template List<
                                             typename K::key>>>::Cons>(ps.v());
          const auto &[x_, gamma] = a0;
          if (K::key_eq_dec(x_, x)) {
            _stack.emplace_back(_Resume1{gamma});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = Datatypes::template List<typename Datatypes::template List<
            typename K::key>>::cons(std::move(_f.gamma), std::move(_result));
      }
    }
    return _result;
  }
};

struct NatKey {
  using key = Datatypes::Nat;
  static bool key_eq_dec(const Datatypes::Nat &n, const Datatypes::Nat &x0);
};

using C = Collector<NatKey>;
const Datatypes::List<C::production> test_prods = Datatypes::template List<
    std::pair<Datatypes::Nat, Datatypes::List<Datatypes::Nat>>>::
    cons(
        std::make_pair(
            Datatypes::Nat::s(Datatypes::Nat::o()),
            Datatypes::template List<Datatypes::Nat>::cons(
                Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                    Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                        Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                            Datatypes::Nat::s(Datatypes::Nat::o())))))))))),
                Datatypes::template List<Datatypes::Nat>::cons(
                    Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                        Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                            Datatypes::Nat::s(Datatypes::Nat::s(
                                Datatypes::Nat::s(Datatypes::Nat::s(
                                    Datatypes::Nat::s(Datatypes::Nat::s(
                                        Datatypes::Nat::s(Datatypes::Nat::s(
                                            Datatypes::Nat::s(Datatypes::Nat::s(
                                                Datatypes::Nat::s(Datatypes::Nat::s(
                                                    Datatypes::Nat::
                                                        s(Datatypes::Nat::s(
                                                            Datatypes::Nat::
                                                                o())))))))))))))))))))),
                    Datatypes::template List<Datatypes::Nat>::nil()))),
        Datatypes::template List<std::
                                     pair<Datatypes::Nat, Datatypes::List<Datatypes::Nat>>>::cons(std::
                                                                                                      make_pair(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::o())), Datatypes::template List<Datatypes::Nat>::cons(Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                Nat::s(Datatypes::
                                                                                                                                                                                                                                                           Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                                                                          Nat::
                                                                                                                                                                                                                                                                                                              s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                Nat::
                                                                                                                                                                                                                                                                                                                                                                                                                                    s(
                                                                                                                                                                                                                                                                                                                                                                                                                                        Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                                              Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      Nat::s(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              Nat::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  s(Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Nat::s(Datatypes::Nat::s(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  Nat::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      s(Datatypes::Nat::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            s(Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        Datatypes::Nat::s(Datatypes::Nat::s(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            Datatypes::Nat::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                o())))))))))))))))))))))))))))))),
                                                                                                                                                                                                                          Datatypes::template List<Datatypes::
                                                                                                                                                                                                                                                       Nat>::nil())),
                                                                                                  Datatypes::template List<std::
                                                                                                                               pair<
                                                                                                                                   Datatypes::Nat, Datatypes::List<Datatypes::Nat>>>::cons(std::make_pair(Datatypes::Nat::s(Datatypes::Nat::o()), Datatypes::
                                                                                                                                                                                                                                                      template List<Datatypes::Nat>::cons(Datatypes::
                                                                                                                                                                                                                                                                                              Nat::
                                                                                                                                                                                                                                                                                                  s(
                                                                                                                                                                                                                                                                                                      Datatypes::
                                                                                                                                                                                                                                                                                                          Nat::s(
                                                                                                                                                                                                                                                                                                              Datatypes::Nat::s(Datatypes::Nat::s(
                                                                                                                                                                                                                                                                                                                  Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                                                                                                        Nat::
                                                                                                                                                                                                                                                                                                                                            s(Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                                                                                                                                    Nat::s(
                                                                                                                                                                                                                                                                                                                                                                        Datatypes::
                                                                                                                                                                                                                                                                                                                                                                            Nat::s(
                                                                                                                                                                                                                                                                                                                                                                                Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                    Nat::s(
                                                                                                                                                                                                                                                                                                                                                                                        Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                            Nat::
                                                                                                                                                                                                                                                                                                                                                                                                s(Datatypes::Nat::
                                                                                                                                                                                                                                                                                                                                                                                                      s(
                                                                                                                                                                                                                                                                                                                                                                                                          Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                Nat::
                                                                                                                                                                                                                                                                                                                                                                                                                                    s(
                                                                                                                                                                                                                                                                                                                                                                                                                                        Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                                              Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         Nat::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             s(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     Nat::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         s(Datatypes::Nat::s(Datatypes::Nat::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 s(Datatypes::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       Nat::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           s(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Datatypes::Nat::o())))))))))))))))))))))))))))))))))))))))),
                                                                                                                                                                                                                                                                                          Datatypes::template List<
                                                                                                                                                                                                                                                                                              Datatypes::Nat>::nil())),
                                                                                                                                                                                           Datatypes::template List<
                                                                                                                                                                                               std::pair<
                                                                                                                                                                                                   Datatypes::
                                                                                                                                                                                                       Nat,
                                                                                                                                                                                                   Datatypes::List<
                                                                                                                                                                                                       Datatypes::
                                                                                                                                                                                                           Nat>>>::
                                                                                                                                                                                               nil())));
const Datatypes::List<Datatypes::List<Datatypes::Nat>> test_result =
    C::rhss_for(test_prods, Datatypes::Nat::s(Datatypes::Nat::o()));

} // namespace PairDerefValue

#endif // INCLUDED_PAIRDEREFVALUE
