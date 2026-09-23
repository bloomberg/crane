#include "alias_minted_before_its_body_type.h"

List<boxed<std::any>>
TFunctor_boxedlist(std::function<std::any(std::any)> f,
                   const List<std::pair<Nat, Exp<std::any>>> &l) {
  return l.template map<std::any>(
      [=]<typename T1>(boxed<T1> _x0) mutable -> boxed<std::any> {
        return bump<std::any, std::any>(f, _x0);
      });
}
