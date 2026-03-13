#include <ram_ops.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<RamOps::ram_bank_main>
RamOps::get_bank_main(const std::shared_ptr<RamOps::state_main> &s,
                      const unsigned int b) {
  return s->ram_sys_main->nth(
      b, std::make_shared<RamOps::ram_bank_main>(ram_bank_main{
             List<std::shared_ptr<RamOps::ram_chip_main>>::ctor::Nil_()}));
}

std::shared_ptr<RamOps::ram_chip_main>
RamOps::get_chip_main(const std::shared_ptr<RamOps::ram_bank_main> &bk,
                      const unsigned int c) {
  return bk->bank_chips_main->nth(
      c, std::make_shared<RamOps::ram_chip_main>(ram_chip_main{
             List<std::shared_ptr<RamOps::ram_reg_main>>::ctor::Nil_()}));
}

std::shared_ptr<RamOps::ram_reg_main>
RamOps::get_reg_main(const std::shared_ptr<RamOps::ram_chip_main> &ch,
                     const unsigned int r) {
  return ch->chip_regs_main->nth(
      r, std::make_shared<RamOps::ram_reg_main>(
             ram_reg_main{List<unsigned int>::ctor::Nil_()}));
}

std::shared_ptr<RamOps::ram_reg_main>
RamOps::upd_main_in_reg(std::shared_ptr<RamOps::ram_reg_main> rg,
                        const unsigned int i, const unsigned int v) {
  return std::make_shared<RamOps::ram_reg_main>(
      ram_reg_main{update_nth_main<unsigned int>(
          std::move(i), (std::move(v) % 16u), std::move(rg)->reg_main)});
}

std::shared_ptr<RamOps::ram_chip_main>
RamOps::upd_reg_in_chip_main(std::shared_ptr<RamOps::ram_chip_main> ch,
                             const unsigned int r,
                             std::shared_ptr<RamOps::ram_reg_main> rg) {
  return std::make_shared<RamOps::ram_chip_main>(
      ram_chip_main{update_nth_main<std::shared_ptr<RamOps::ram_reg_main>>(
          std::move(r), std::move(rg), std::move(ch)->chip_regs_main)});
}

std::shared_ptr<RamOps::ram_bank_main>
RamOps::upd_chip_in_bank_main(std::shared_ptr<RamOps::ram_bank_main> bk,
                              const unsigned int c,
                              std::shared_ptr<RamOps::ram_chip_main> ch) {
  return std::make_shared<RamOps::ram_bank_main>(
      ram_bank_main{update_nth_main<std::shared_ptr<RamOps::ram_chip_main>>(
          std::move(c), std::move(ch), std::move(bk)->bank_chips_main)});
}

std::shared_ptr<List<std::shared_ptr<RamOps::ram_bank_main>>>
RamOps::upd_bank_in_sys_main(const std::shared_ptr<RamOps::state_main> &s,
                             const unsigned int b,
                             const std::shared_ptr<RamOps::ram_bank_main> &bk) {
  return update_nth_main<std::shared_ptr<RamOps::ram_bank_main>>(
      b, bk, s->ram_sys_main);
}

std::shared_ptr<List<std::shared_ptr<RamOps::ram_bank_main>>>
RamOps::ram_write_main_sys(const std::shared_ptr<RamOps::state_main> &s,
                           const unsigned int v) {
  unsigned int b = s->cur_bank_main;
  unsigned int c = s->sel_chip_main;
  unsigned int r = s->sel_reg_main;
  unsigned int i = s->sel_char_main;
  std::shared_ptr<RamOps::ram_bank_main> bk = get_bank_main(s, std::move(b));
  std::shared_ptr<RamOps::ram_chip_main> ch =
      get_chip_main(std::move(bk), std::move(c));
  std::shared_ptr<RamOps::ram_reg_main> rg =
      get_reg_main(std::move(ch), std::move(r));
  std::shared_ptr<RamOps::ram_reg_main> rg_ =
      upd_main_in_reg(std::move(rg), std::move(i), v);
  std::shared_ptr<RamOps::ram_chip_main> ch_ =
      upd_reg_in_chip_main(std::move(ch), std::move(r), std::move(rg_));
  std::shared_ptr<RamOps::ram_bank_main> bk_ =
      upd_chip_in_bank_main(std::move(bk), std::move(c), std::move(ch_));
  return upd_bank_in_sys_main(s, std::move(b), std::move(bk_));
}

std::shared_ptr<RamOps::bank_port>
RamOps::get_bank_port(const std::shared_ptr<RamOps::state_port> &s,
                      const unsigned int b) {
  return s->ram_sys_port->nth(
      b, std::make_shared<RamOps::bank_port>(bank_port{
             List<std::shared_ptr<RamOps::chip_port>>::ctor::Nil_()}));
}

std::shared_ptr<RamOps::chip_port>
RamOps::get_chip_port(const std::shared_ptr<RamOps::bank_port> &bk,
                      const unsigned int c) {
  return bk->bank_chips_port->nth(
      c, std::make_shared<RamOps::chip_port>(chip_port{0u}));
}

std::shared_ptr<RamOps::chip_port>
RamOps::upd_port_in_chip(const std::shared_ptr<RamOps::chip_port> &_x,
                         const unsigned int v) {
  return std::make_shared<RamOps::chip_port>(chip_port{(std::move(v) % 16u)});
}

std::shared_ptr<RamOps::bank_port>
RamOps::upd_chip_in_bank_port(std::shared_ptr<RamOps::bank_port> bk,
                              const unsigned int c,
                              std::shared_ptr<RamOps::chip_port> ch) {
  return std::make_shared<RamOps::bank_port>(
      bank_port{update_nth_port<std::shared_ptr<RamOps::chip_port>>(
          std::move(c), std::move(ch), std::move(bk)->bank_chips_port)});
}

std::shared_ptr<List<std::shared_ptr<RamOps::bank_port>>>
RamOps::upd_bank_in_sys_port(const std::shared_ptr<RamOps::state_port> &s,
                             const unsigned int b,
                             const std::shared_ptr<RamOps::bank_port> &bk) {
  return update_nth_port<std::shared_ptr<RamOps::bank_port>>(b, bk,
                                                             s->ram_sys_port);
}

std::shared_ptr<List<std::shared_ptr<RamOps::bank_port>>>
RamOps::ram_write_port_sys(const std::shared_ptr<RamOps::state_port> &s,
                           const unsigned int v) {
  unsigned int b = s->cur_bank_port;
  unsigned int c = s->sel_chip_port;
  std::shared_ptr<RamOps::bank_port> bk = get_bank_port(s, std::move(b));
  std::shared_ptr<RamOps::chip_port> ch =
      get_chip_port(std::move(bk), std::move(c));
  std::shared_ptr<RamOps::chip_port> ch_ = upd_port_in_chip(std::move(ch), v);
  std::shared_ptr<RamOps::bank_port> bk_ =
      upd_chip_in_bank_port(std::move(bk), std::move(c), std::move(ch_));
  return upd_bank_in_sys_port(s, std::move(b), std::move(bk_));
}

std::shared_ptr<RamOps::ram_bank_status>
RamOps::get_bank_status(const std::shared_ptr<RamOps::state_status> &s,
                        const unsigned int b) {
  return s->ram_sys_status->nth(
      b, std::make_shared<RamOps::ram_bank_status>(ram_bank_status{
             List<std::shared_ptr<RamOps::ram_chip_status>>::ctor::Nil_()}));
}

std::shared_ptr<RamOps::ram_chip_status>
RamOps::get_chip_status(const std::shared_ptr<RamOps::ram_bank_status> &bk,
                        const unsigned int c) {
  return bk->bank_chips_status->nth(
      c, std::make_shared<RamOps::ram_chip_status>(ram_chip_status{
             List<std::shared_ptr<RamOps::ram_reg_status>>::ctor::Nil_()}));
}

std::shared_ptr<RamOps::ram_reg_status>
RamOps::get_reg_status(const std::shared_ptr<RamOps::ram_chip_status> &ch,
                       const unsigned int r) {
  return ch->chip_regs_status->nth(
      r, std::make_shared<RamOps::ram_reg_status>(
             ram_reg_status{List<unsigned int>::ctor::Nil_()}));
}

std::shared_ptr<RamOps::ram_reg_status>
RamOps::upd_status_in_reg(std::shared_ptr<RamOps::ram_reg_status> rg,
                          const unsigned int i, const unsigned int v) {
  return std::make_shared<RamOps::ram_reg_status>(
      ram_reg_status{update_nth_status<unsigned int>(
          std::move(i), (std::move(v) % 16u), std::move(rg)->reg_status)});
}

std::shared_ptr<RamOps::ram_chip_status>
RamOps::upd_reg_in_chip_status(std::shared_ptr<RamOps::ram_chip_status> ch,
                               const unsigned int r,
                               std::shared_ptr<RamOps::ram_reg_status> rg) {
  return std::make_shared<RamOps::ram_chip_status>(ram_chip_status{
      update_nth_status<std::shared_ptr<RamOps::ram_reg_status>>(
          std::move(r), std::move(rg), std::move(ch)->chip_regs_status)});
}

std::shared_ptr<RamOps::ram_bank_status>
RamOps::upd_chip_in_bank_status(std::shared_ptr<RamOps::ram_bank_status> bk,
                                const unsigned int c,
                                std::shared_ptr<RamOps::ram_chip_status> ch) {
  return std::make_shared<RamOps::ram_bank_status>(ram_bank_status{
      update_nth_status<std::shared_ptr<RamOps::ram_chip_status>>(
          std::move(c), std::move(ch), std::move(bk)->bank_chips_status)});
}

std::shared_ptr<List<std::shared_ptr<RamOps::ram_bank_status>>>
RamOps::upd_bank_in_sys_status(
    const std::shared_ptr<RamOps::state_status> &s, const unsigned int b,
    const std::shared_ptr<RamOps::ram_bank_status> &bk) {
  return update_nth_status<std::shared_ptr<RamOps::ram_bank_status>>(
      b, bk, s->ram_sys_status);
}

std::shared_ptr<List<std::shared_ptr<RamOps::ram_bank_status>>>
RamOps::ram_write_status_sys(const std::shared_ptr<RamOps::state_status> &s,
                             const unsigned int idx, const unsigned int v) {
  unsigned int b = s->cur_bank_status;
  unsigned int c = s->sel_chip_status;
  unsigned int r = s->sel_reg_status;
  std::shared_ptr<RamOps::ram_bank_status> bk =
      get_bank_status(s, std::move(b));
  std::shared_ptr<RamOps::ram_chip_status> ch =
      get_chip_status(std::move(bk), std::move(c));
  std::shared_ptr<RamOps::ram_reg_status> rg =
      get_reg_status(std::move(ch), std::move(r));
  std::shared_ptr<RamOps::ram_reg_status> rg_ =
      upd_status_in_reg(std::move(rg), idx, v);
  std::shared_ptr<RamOps::ram_chip_status> ch_ =
      upd_reg_in_chip_status(std::move(ch), std::move(r), std::move(rg_));
  std::shared_ptr<RamOps::ram_bank_status> bk_ =
      upd_chip_in_bank_status(std::move(bk), std::move(c), std::move(ch_));
  return upd_bank_in_sys_status(s, std::move(b), std::move(bk_));
}

std::shared_ptr<RamOps::ram_bank_sel>
RamOps::get_bank_sel(const std::shared_ptr<RamOps::state_sel> &s,
                     const unsigned int b) {
  return s->ram_sys_sel->nth(b, empty_bank_sel);
}

std::shared_ptr<RamOps::ram_chip_sel>
RamOps::get_chip_sel(const std::shared_ptr<RamOps::ram_bank_sel> &bk,
                     const unsigned int c) {
  return bk->bank_chips_sel->nth(c, empty_chip_sel);
}

std::shared_ptr<RamOps::ram_reg_sel>
RamOps::get_regRAM(const std::shared_ptr<RamOps::ram_chip_sel> &ch,
                   const unsigned int r) {
  return ch->chip_regs_sel->nth(r, empty_reg_sel);
}

__attribute__((pure)) unsigned int
RamOps::get_main_sel(const std::shared_ptr<RamOps::ram_reg_sel> &rg,
                     const unsigned int i) {
  return rg->reg_main_sel->nth(i, 0u);
}

__attribute__((pure)) unsigned int
RamOps::ram_read_main(const std::shared_ptr<RamOps::state_sel> &s) {
  std::shared_ptr<RamOps::ram_bank_sel> bk = get_bank_sel(s, s->cur_bank_sel);
  std::shared_ptr<RamOps::ram_chip_sel> ch =
      get_chip_sel(std::move(bk), s->sel_ram->sel_chip);
  std::shared_ptr<RamOps::ram_reg_sel> rg =
      get_regRAM(std::move(ch), s->sel_ram->sel_reg);
  return get_main_sel(std::move(rg), s->sel_ram->sel_char);
}

std::shared_ptr<RamOps::ram_bank_nested>
RamOps::get_bank_nested(const std::shared_ptr<RamOps::state_nested> &s,
                        const unsigned int b) {
  return s->ram_sys_nested->nth(b, empty_bank_nested);
}

std::shared_ptr<RamOps::ram_chip_nested>
RamOps::get_chip_nested(const std::shared_ptr<RamOps::ram_bank_nested> &bk,
                        const unsigned int c) {
  return bk->bank_chips_nested->nth(c, empty_chip_nested);
}

std::shared_ptr<RamOps::ram_reg_nested>
RamOps::get_regRAM_nested(const std::shared_ptr<RamOps::ram_chip_nested> &ch,
                          const unsigned int r) {
  return ch->chip_regs_nested->nth(r, empty_reg_nested);
}

__attribute__((pure)) unsigned int
RamOps::get_main_nested(const std::shared_ptr<RamOps::ram_reg_nested> &rg,
                        const unsigned int i) {
  return rg->reg_main_nested->nth(i, 0u);
}

__attribute__((pure)) unsigned int
RamOps::ram_read_main_nested(const std::shared_ptr<RamOps::state_nested> &s) {
  std::shared_ptr<RamOps::ram_bank_nested> bk =
      get_bank_nested(s, s->cur_bank_nested);
  std::shared_ptr<RamOps::ram_chip_nested> ch =
      get_chip_nested(std::move(bk), s->sel_ram_nested->sel_chip_nested);
  std::shared_ptr<RamOps::ram_reg_nested> rg =
      get_regRAM_nested(std::move(ch), s->sel_ram_nested->sel_reg_nested);
  return get_main_nested(std::move(rg), s->sel_ram_nested->sel_char_nested);
}

__attribute__((pure)) RamOps::reg_frame
RamOps::upd_main_in_reg_frame(const std::shared_ptr<List<unsigned int>> &rg,
                              const unsigned int i, const unsigned int v) {
  return update_nth_frame<unsigned int>(i, v, rg);
}

__attribute__((pure)) RamOps::chip_frame RamOps::upd_reg_in_chip_frame(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ch,
    const unsigned int r, const std::shared_ptr<List<unsigned int>> &rg) {
  return update_nth_frame<RamOps::reg_frame>(r, rg, ch);
}

__attribute__((pure)) RamOps::bank_frame RamOps::upd_chip_in_bank_frame(
    const std::shared_ptr<
        List<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>>> &bk,
    const unsigned int c,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ch) {
  return update_nth_frame<RamOps::chip_frame>(c, ch, bk);
}

std::shared_ptr<List<unsigned int>> RamOps::ram_write_main_sys_preserve(
    const std::shared_ptr<RamOps::state_preserve> &s, const unsigned int v) {
  return update_nth_preserve<unsigned int>(s->cur_bank_preserve, v,
                                           s->ram_sys_preserve);
}

std::shared_ptr<RamOps::state_preserve>
RamOps::execute_write(std::shared_ptr<RamOps::state_preserve> s,
                      const unsigned int v) {
  return std::make_shared<RamOps::state_preserve>(state_preserve{
      ram_write_main_sys_preserve(s, std::move(v)), s->cur_bank_preserve});
}

__attribute__((pure)) bool
RamOps::ram_addr_disjointb(const unsigned int b1, const unsigned int c1,
                           const unsigned int r1, const unsigned int i1,
                           const unsigned int b2, const unsigned int c2,
                           const unsigned int r2, const unsigned int i2) {
  return !((((b1 == b2 && c1 == c2) && r1 == r2) && i1 == i2));
}

std::shared_ptr<RamOps::bank_nested_bank>
RamOps::get_bank0(const std::shared_ptr<RamOps::state_nested_bank> &s) {
  return s->banks_->nth(
      0u, std::make_shared<RamOps::bank_nested_bank>(bank_nested_bank{
              List<std::shared_ptr<RamOps::chip_nested_bank>>::ctor::Nil_()}));
}

std::shared_ptr<RamOps::chip_nested_bank>
RamOps::get_chip0(const std::shared_ptr<RamOps::bank_nested_bank> &b) {
  return b->chips_->nth(
      0u, std::make_shared<RamOps::chip_nested_bank>(chip_nested_bank{
              List<std::shared_ptr<RamOps::reg_nested_bank>>::ctor::Nil_()}));
}

std::shared_ptr<RamOps::reg_nested_bank>
RamOps::get_reg0(const std::shared_ptr<RamOps::chip_nested_bank> &c) {
  return c->regs_->nth(0u,
                       std::make_shared<RamOps::reg_nested_bank>(
                           reg_nested_bank{List<unsigned int>::ctor::Nil_()}));
}

std::shared_ptr<RamOps::state_nested_bank>
RamOps::write_status0(std::shared_ptr<RamOps::state_nested_bank> s,
                      const unsigned int v) {
  std::shared_ptr<RamOps::bank_nested_bank> b = get_bank0(std::move(s));
  std::shared_ptr<RamOps::chip_nested_bank> c = get_chip0(std::move(b));
  std::shared_ptr<RamOps::reg_nested_bank> r = get_reg0(std::move(c));
  std::shared_ptr<RamOps::reg_nested_bank> r_ =
      std::make_shared<RamOps::reg_nested_bank>(
          reg_nested_bank{update_nth_nested_bank<unsigned int>(
              0u, std::move(v), std::move(r)->status_)});
  std::shared_ptr<RamOps::chip_nested_bank> c_ =
      std::make_shared<RamOps::chip_nested_bank>(chip_nested_bank{
          update_nth_nested_bank<std::shared_ptr<RamOps::reg_nested_bank>>(
              0u, std::move(r_), std::move(c)->regs_)});
  std::shared_ptr<RamOps::bank_nested_bank> b_ =
      std::make_shared<RamOps::bank_nested_bank>(bank_nested_bank{
          update_nth_nested_bank<std::shared_ptr<RamOps::chip_nested_bank>>(
              0u, std::move(c_), std::move(b)->chips_)});
  return std::make_shared<RamOps::state_nested_bank>(state_nested_bank{
      update_nth_nested_bank<std::shared_ptr<RamOps::bank_nested_bank>>(
          0u, std::move(b_), std::move(s)->banks_)});
}

__attribute__((pure)) unsigned int
RamOps::read_status0(const std::shared_ptr<RamOps::state_nested_bank> &s) {
  std::shared_ptr<RamOps::bank_nested_bank> b = get_bank0(s);
  std::shared_ptr<RamOps::chip_nested_bank> c = get_chip0(std::move(b));
  std::shared_ptr<RamOps::reg_nested_bank> r = get_reg0(std::move(c));
  return std::move(r)->status_->nth(0u, 0u);
}

__attribute__((pure)) unsigned int RamOps::score(const RamOps::Item x) {
  return [&](void) {
    switch (x) {
    case Item::e_S_: {
      return 1u;
    }
    case Item::e_S_0: {
      return 2u;
    }
    }
  }();
}
