#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nested_bank_status_write.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> NestedBankStatusWrite::status_(
    const std::shared_ptr<NestedBankStatusWrite::reg> &r) {
  return r->status_;
}

std::shared_ptr<List<std::shared_ptr<NestedBankStatusWrite::reg>>>
NestedBankStatusWrite::regs_(
    const std::shared_ptr<NestedBankStatusWrite::chip> &c) {
  return c->regs_;
}

std::shared_ptr<List<std::shared_ptr<NestedBankStatusWrite::chip>>>
NestedBankStatusWrite::chips_(
    const std::shared_ptr<NestedBankStatusWrite::bank> &b) {
  return b->chips_;
}

std::shared_ptr<List<std::shared_ptr<NestedBankStatusWrite::bank>>>
NestedBankStatusWrite::banks_(
    const std::shared_ptr<NestedBankStatusWrite::state> &s) {
  return s->banks_;
}

std::shared_ptr<NestedBankStatusWrite::bank> NestedBankStatusWrite::get_bank0(
    const std::shared_ptr<NestedBankStatusWrite::state> &s) {
  return s->banks_->nth(
      0,
      std::make_shared<NestedBankStatusWrite::bank>(bank{
          List<std::shared_ptr<NestedBankStatusWrite::chip>>::ctor::nil_()}));
}

std::shared_ptr<NestedBankStatusWrite::chip> NestedBankStatusWrite::get_chip0(
    const std::shared_ptr<NestedBankStatusWrite::bank> &b) {
  return b->chips_->nth(
      0, std::make_shared<NestedBankStatusWrite::chip>(chip{
             List<std::shared_ptr<NestedBankStatusWrite::reg>>::ctor::nil_()}));
}

std::shared_ptr<NestedBankStatusWrite::reg> NestedBankStatusWrite::get_reg0(
    const std::shared_ptr<NestedBankStatusWrite::chip> &c) {
  return c->regs_->nth(0, std::make_shared<NestedBankStatusWrite::reg>(
                              reg{List<unsigned int>::ctor::nil_()}));
}

std::shared_ptr<NestedBankStatusWrite::state>
NestedBankStatusWrite::write_status0(
    std::shared_ptr<NestedBankStatusWrite::state> s, const unsigned int v) {
  std::shared_ptr<NestedBankStatusWrite::bank> b = get_bank0(std::move(s));
  std::shared_ptr<NestedBankStatusWrite::chip> c = get_chip0(std::move(b));
  std::shared_ptr<NestedBankStatusWrite::reg> r = get_reg0(std::move(c));
  std::shared_ptr<NestedBankStatusWrite::reg> r_ =
      std::make_shared<NestedBankStatusWrite::reg>(reg{
          update_nth<unsigned int>(0, std::move(v), std::move(r)->status_)});
  std::shared_ptr<NestedBankStatusWrite::chip> c_ =
      std::make_shared<NestedBankStatusWrite::chip>(
          chip{update_nth<std::shared_ptr<NestedBankStatusWrite::reg>>(
              0, std::move(r_), std::move(c)->regs_)});
  std::shared_ptr<NestedBankStatusWrite::bank> b_ =
      std::make_shared<NestedBankStatusWrite::bank>(
          bank{update_nth<std::shared_ptr<NestedBankStatusWrite::chip>>(
              0, std::move(c_), std::move(b)->chips_)});
  return std::make_shared<NestedBankStatusWrite::state>(
      state{update_nth<std::shared_ptr<NestedBankStatusWrite::bank>>(
          0, std::move(b_), std::move(s)->banks_)});
}

unsigned int NestedBankStatusWrite::read_status0(
    const std::shared_ptr<NestedBankStatusWrite::state> &s) {
  std::shared_ptr<NestedBankStatusWrite::bank> b = get_bank0(s);
  std::shared_ptr<NestedBankStatusWrite::chip> c = get_chip0(std::move(b));
  std::shared_ptr<NestedBankStatusWrite::reg> r = get_reg0(std::move(c));
  return std::move(r)->status_->nth(0, 0);
}
