#include <wpm_ops.h>

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

__attribute__((pure)) bool
WpmOps::nat_list_eqb(const std::shared_ptr<List<unsigned int>> &xs,
                     const std::shared_ptr<List<unsigned int>> &ys) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::Nil _args) -> bool {
                      return true;
                    },
                    [](const typename List<unsigned int>::Cons _args) -> bool {
                      return false;
                    }},
                ys->v());
          },
          [&](const typename List<unsigned int>::Cons _args) -> bool {
            unsigned int x = _args.d_a0;
            std::shared_ptr<List<unsigned int>> xs_ = _args.d_a1;
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::Nil _args) -> bool {
                      return false;
                    },
                    [&](const typename List<unsigned int>::Cons _args) -> bool {
                      unsigned int y = _args.d_a0;
                      std::shared_ptr<List<unsigned int>> ys_ = _args.d_a1;
                      return (std::move(x) == std::move(y) &&
                              nat_list_eqb(std::move(xs_), std::move(ys_)));
                    }},
                ys->v());
          }},
      xs->v());
}

std::shared_ptr<WpmOps::state1>
WpmOps::execute_wpm1(std::shared_ptr<WpmOps::state1> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable1) {
    new_rom = update_nth<unsigned int>(s->prom_addr1, s->prom_data1, s->rom1);
  } else {
    new_rom = std::move(s)->rom1;
  }
  return std::make_shared<WpmOps::state1>(state1{
      std::move(new_rom), s->prom_addr1, s->prom_data1, s->prom_enable1});
}

std::shared_ptr<WpmOps::state2>
WpmOps::execute_wpm2(std::shared_ptr<WpmOps::state2> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable2) {
    new_rom = update_nth<unsigned int>(s->prom_addr2, s->prom_data2, s->rom2);
  } else {
    new_rom = std::move(s)->rom2;
  }
  return std::make_shared<WpmOps::state2>(
      state2{s->ram_sys2, std::move(new_rom), s->prom_addr2, s->prom_data2,
             s->prom_enable2});
}

std::shared_ptr<WpmOps::state3>
WpmOps::execute_wpm3(std::shared_ptr<WpmOps::state3> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable3) {
    new_rom = update_nth<unsigned int>(s->prom_addr3, s->prom_data3, s->rom3);
  } else {
    new_rom = std::move(s)->rom3;
  }
  return std::make_shared<WpmOps::state3>(state3{s->regs3, std::move(new_rom),
                                                 s->prom_addr3, s->prom_data3,
                                                 s->prom_enable3});
}

std::shared_ptr<WpmOps::state4>
WpmOps::execute_wpm4(std::shared_ptr<WpmOps::state4> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable4) {
    new_rom = update_nth<unsigned int>(s->prom_addr4, s->prom_data4, s->rom4);
  } else {
    new_rom = std::move(s)->rom4;
  }
  return std::make_shared<WpmOps::state4>(state4{
      std::move(new_rom), s->prom_addr4, s->prom_data4, s->prom_enable4});
}

std::shared_ptr<WpmOps::state5>
WpmOps::execute_wpm5(std::shared_ptr<WpmOps::state5> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable5) {
    new_rom = update_nth<unsigned int>(s->prom_addr5, s->prom_data5, s->rom5);
  } else {
    new_rom = std::move(s)->rom5;
  }
  return std::make_shared<WpmOps::state5>(state5{
      std::move(new_rom), s->prom_addr5, s->prom_data5, s->prom_enable5});
}

std::shared_ptr<WpmOps::state6>
WpmOps::execute_wpm6(std::shared_ptr<WpmOps::state6> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable6) {
    new_rom = update_nth<unsigned int>(s->prom_addr6, s->prom_data6, s->rom6);
  } else {
    new_rom = std::move(s)->rom6;
  }
  return std::make_shared<WpmOps::state6>(state6{
      std::move(new_rom), s->prom_addr6, s->prom_data6, s->prom_enable6});
}
