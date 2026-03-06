#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_port_write_chain.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int RamPortWriteChain::chip_port(
    const std::shared_ptr<RamPortWriteChain::chip> &c) {
  return c->chip_port;
}

std::shared_ptr<List<std::shared_ptr<RamPortWriteChain::chip>>>
RamPortWriteChain::bank_chips(
    const std::shared_ptr<RamPortWriteChain::bank> &b) {
  return b->bank_chips;
}

std::shared_ptr<List<std::shared_ptr<RamPortWriteChain::bank>>>
RamPortWriteChain::ram_sys(const std::shared_ptr<RamPortWriteChain::state> &s) {
  return s->ram_sys;
}

unsigned int RamPortWriteChain::cur_bank(
    const std::shared_ptr<RamPortWriteChain::state> &s) {
  return s->cur_bank;
}

unsigned int RamPortWriteChain::sel_chip(
    const std::shared_ptr<RamPortWriteChain::state> &s) {
  return s->sel_chip;
}

std::shared_ptr<RamPortWriteChain::bank>
RamPortWriteChain::get_bank(const std::shared_ptr<RamPortWriteChain::state> &s,
                            const unsigned int b) {
  return s->ram_sys->nth(
      b, std::make_shared<RamPortWriteChain::bank>(bank{
             List<std::shared_ptr<RamPortWriteChain::chip>>::ctor::nil_()}));
}

std::shared_ptr<RamPortWriteChain::chip>
RamPortWriteChain::get_chip(const std::shared_ptr<RamPortWriteChain::bank> &bk,
                            const unsigned int c) {
  return bk->bank_chips->nth(
      c, std::make_shared<RamPortWriteChain::chip>(chip{0}));
}

std::shared_ptr<RamPortWriteChain::chip> RamPortWriteChain::upd_port_in_chip(
    const std::shared_ptr<RamPortWriteChain::chip> &_x, const unsigned int v) {
  return std::make_shared<RamPortWriteChain::chip>(chip{(
      std::move(v) %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1))});
}

std::shared_ptr<RamPortWriteChain::bank> RamPortWriteChain::upd_chip_in_bank(
    std::shared_ptr<RamPortWriteChain::bank> bk, const unsigned int c,
    std::shared_ptr<RamPortWriteChain::chip> ch) {
  return std::make_shared<RamPortWriteChain::bank>(
      bank{update_nth<std::shared_ptr<RamPortWriteChain::chip>>(
          std::move(c), std::move(ch), std::move(bk)->bank_chips)});
}

std::shared_ptr<List<std::shared_ptr<RamPortWriteChain::bank>>>
RamPortWriteChain::upd_bank_in_sys(
    const std::shared_ptr<RamPortWriteChain::state> &s, const unsigned int b,
    const std::shared_ptr<RamPortWriteChain::bank> &bk) {
  return update_nth<std::shared_ptr<RamPortWriteChain::bank>>(b, bk,
                                                              s->ram_sys);
}

std::shared_ptr<List<std::shared_ptr<RamPortWriteChain::bank>>>
RamPortWriteChain::ram_write_port_sys(
    const std::shared_ptr<RamPortWriteChain::state> &s, const unsigned int v) {
  unsigned int b = s->cur_bank;
  unsigned int c = s->sel_chip;
  std::shared_ptr<RamPortWriteChain::bank> bk = get_bank(s, std::move(b));
  std::shared_ptr<RamPortWriteChain::chip> ch =
      get_chip(std::move(bk), std::move(c));
  std::shared_ptr<RamPortWriteChain::chip> ch_ =
      upd_port_in_chip(std::move(ch), v);
  std::shared_ptr<RamPortWriteChain::bank> bk_ =
      upd_chip_in_bank(std::move(bk), std::move(c), std::move(ch_));
  return upd_bank_in_sys(s, std::move(b), std::move(bk_));
}
