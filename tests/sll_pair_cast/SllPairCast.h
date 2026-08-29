#ifndef INCLUDED_SLLPAIRCAST
#define INCLUDED_SLLPAIRCAST

#include <any>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace SllPairCast {

struct SllPairCast {
  struct sll_frame {
    std::optional<uint64_t> fr_ret;
    Datatypes::List<uint64_t> fr_suf;
  };

  using sll_stack = std::pair<sll_frame, Datatypes::List<sll_frame>>;

  struct sll_subparser {
    Datatypes::List<uint64_t> sll_pred;
    sll_stack sll_stk;
  };

  static bool sll_final_config(const sll_subparser &sp);

  static const bool &test_final() {
    static const bool v = sll_final_config(sll_subparser{
        Datatypes::template List<uint64_t>::cons(
            UINT64_C(1),
            Datatypes::template List<uint64_t>::cons(
                UINT64_C(2), Datatypes::template List<uint64_t>::nil())),
        std::make_pair(sll_frame{std::optional<uint64_t>(),
                                 Datatypes::template List<uint64_t>::nil()},
                       Datatypes::template List<sll_frame>::nil())});
    return v;
  }

  static const bool &test_not_final() {
    static const bool v = sll_final_config(sll_subparser{
        Datatypes::template List<uint64_t>::nil(),
        std::make_pair(
            sll_frame{
                std::make_optional<uint64_t>(UINT64_C(5)),
                Datatypes::template List<uint64_t>::cons(
                    UINT64_C(1), Datatypes::template List<uint64_t>::nil())},
            Datatypes::template List<sll_frame>::cons(
                sll_frame{std::optional<uint64_t>(),
                          Datatypes::template List<uint64_t>::nil()},
                Datatypes::template List<sll_frame>::nil()))});
    return v;
  }
};

} // namespace SllPairCast

#endif // INCLUDED_SLLPAIRCAST
