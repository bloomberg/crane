#include <functional>
#include <iostream>
#include <memory>
#include <rapply.h>
#include <string>
#include <variant>

std::shared_ptr<Nat::nat> RApply::f(const std::shared_ptr<RApply::r> &r,
                                    const std::shared_ptr<Nat::nat> &_x0,
                                    const std::shared_ptr<Nat::nat> &_x1) {
  return r->f(_x0, _x1);
}

std::shared_ptr<Nat::nat> RApply::_tag(const std::shared_ptr<RApply::r> &r) {
  return r->_tag;
}

std::shared_ptr<Nat::nat>
RApply::apply_record(const std::shared_ptr<RApply::r> &r,
                     const std::shared_ptr<Nat::nat> &a,
                     const std::shared_ptr<Nat::nat> &b) {
  return r->f(a, b);
}
