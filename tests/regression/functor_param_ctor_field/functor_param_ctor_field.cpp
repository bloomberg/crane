#include "functor_param_ctor_field.h"

/// A constructor field whose type is a custom applied to a functor's
/// parameter type: lhs : option nt, option a custom, its inductive
/// declared in the parameter's signature.  Extraction carried the type
/// argument nt among the custom's term arguments too, and the field's
/// conversion read it as a value -- a callee no callable plan exists for.
/// From ParseALot's SllOptimizationSound.
uint64_t FunctorParamCtorField::made_depth(bool b) {
  return NamesImpl::depth(NamesImpl::mk(b));
}
