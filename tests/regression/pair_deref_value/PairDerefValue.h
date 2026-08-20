#ifndef INCLUDED_PAIRDEREFVALUE
#define INCLUDED_PAIRDEREFVALUE

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

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
      typename K::key x) {
    std::shared_ptr<typename Datatypes::template List<
        typename Datatypes::template List<typename K::key>>>
        _head{};
    std::shared_ptr<typename Datatypes::template List<
        typename Datatypes::template List<typename K::key>>> *_write = &_head;
    const typename Datatypes::template List<std::pair<
        typename K::key, typename Datatypes::template List<typename K::key>>>
        *_loop_ps = &ps;
    while (true) {
      if (std::holds_alternative<typename Datatypes::template List<std::pair<
              typename K::key,
              typename Datatypes::template List<typename K::key>>>::Nil>(
              _loop_ps->v())) {
        *_write = std::make_shared<typename Datatypes::template List<
            typename Datatypes::template List<typename K::key>>>(
            Datatypes::template List<
                typename Datatypes::template List<typename K::key>>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename Datatypes::template List<std::pair<
                typename K::key,
                typename Datatypes::template List<typename K::key>>>::Cons>(
                _loop_ps->v());
        const auto &[x_, gamma] = a0;
        if (K::key_eq_dec(x_, x)) {
          auto _cell = std::make_shared<typename Datatypes::template List<
              typename Datatypes::template List<typename K::key>>>(
              typename Datatypes::template List<
                  typename Datatypes::template List<typename K::key>>::
                  Cons(gamma, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename Datatypes::template List<
              typename Datatypes::template List<typename K::key>>::Cons>(
                        (*_write)->v_mut())
                        .l;
          _loop_ps = crane_raw(a1);
          continue;
        } else {
          _loop_ps = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
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
