#include "Datatypes.h"

namespace Datatypes {

bool implb(bool b1, bool b2) {
  if (b1) {
    return b2;
  } else {
    return true;
  }
}

bool xorb(bool b1, bool b2) {
  if (b1) {
    if (b2) {
      return false;
    } else {
      return true;
    }
  } else {
    return b2;
  }
}

Comparison CompOpp(Comparison r) {
  switch (r) {
  case Comparison::EQ: {
    return Comparison::EQ;
  }
  case Comparison::LT: {
    return Comparison::GT;
  }
  case Comparison::GT: {
    return Comparison::LT;
  }
  default:
    std::unreachable();
  }
}

CompareSpecT CompareSpec2Type(Comparison c) {
  switch (c) {
  case Comparison::EQ: {
    return CompareSpecT::COMPEQT;
  }
  case Comparison::LT: {
    return CompareSpecT::COMPLTT;
  }
  case Comparison::GT: {
    return CompareSpecT::COMPGTT;
  }
  default:
    std::unreachable();
  }
}

crane::obj id(crane::obj x) { return x; }

} // namespace Datatypes
