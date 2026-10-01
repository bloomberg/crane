#include "alias_minted_before_its_body_type.h"

List<boxed<crane::obj>>
TFunctor_boxedlist(crane::fn<crane::obj(crane::obj)> f,
                   const List<std::pair<Nat, Exp<crane::obj>>> &l) {
  return l.template map<boxed<crane::obj>>(
      [=]<typename T1>(boxed<T1> _x0) -> boxed<crane::obj> {
        return bump<crane::obj, crane::obj>(f, _x0);
      });
}
