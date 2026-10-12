#ifndef INCLUDED_RANK2_ALIAS_DEFINITION_AS_VALUE
#define INCLUDED_RANK2_ALIAS_DEFINITION_AS_VALUE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "shared_block.h"
#include <cstdint>

struct Nat {};

struct Rank2AliasDefinitionAsValue {
  template <typename a>
  using clist =
      crane::fn<crane::obj(crane::fn<crane::obj(a, crane::obj)>, crane::obj)>;

  template <typename T1 = void, typename F0>
  static crane::obj cnil(F0 &&, crane::obj n) {
    return n;
  }

  static uint64_t csum(clist<uint64_t> l);
  using nfold = crane::fn<crane::obj(
      crane::fn<crane::obj(uint64_t, crane::obj)>, crane::obj)>;

  template <typename F0> static crane::obj fnil(F0 &&, crane::obj n) {
    return n;
  }

  static uint64_t fsum(nfold l);
  template <typename a>
  using box = crane::fn<crane::obj(crane::fn<crane::obj(a)>)>;

  template <typename F0> static crane::obj bnat(F0 &&k) {
    return k(UINT64_C(3));
  }

  static uint64_t unbox(box<uint64_t> b);
  static inline const uint64_t result =
      ((csum(crane_erase_fn<crane::obj>(
            [](crane::fn<crane::obj(uint64_t, crane::obj)> _ec0,
               crane::obj _ec1) { return cnil<uint64_t>(_ec0, _ec1); })) +
        fsum(crane_erase_fn<crane::obj>(
            [](crane::fn<crane::obj(uint64_t, crane::obj)> _ec0,
               crane::obj _ec1) { return fnil(_ec0, _ec1); }))) +
       unbox(crane_convert<
             crane::fn<crane::obj(crane::fn<crane::obj(uint64_t)>)>>(
           [](crane::fn<crane::obj(uint64_t)> _ec0) { return bnat(_ec0); })));
};

#endif // INCLUDED_RANK2_ALIAS_DEFINITION_AS_VALUE
