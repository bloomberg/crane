#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <load_program_head_write.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
LoadProgramHeadWrite::update_nth(const unsigned int n, const unsigned int x,
                                 std::shared_ptr<List<unsigned int>> l) {
  if (n <= 0) {
    return [&](void) {
      if (((l.use_count() == 1) && (l->v().index() == 1))) {
        auto &_rf = std::get<1>(l->v_mut());
        std::shared_ptr<List<unsigned int>> xs = std::move(_rf._a1);
        _rf._a0 = x;
        _rf._a1 = xs;
        return l;
      } else {
        return std::visit(
            Overloaded{[&](const typename List<unsigned int>::nil _args)
                           -> std::shared_ptr<List<unsigned int>> {
                         return std::move(l);
                       },
                       [&](const typename List<unsigned int>::cons _args)
                           -> std::shared_ptr<List<unsigned int>> {
                         std::shared_ptr<List<unsigned int>> xs = _args._a1;
                         return List<unsigned int>::ctor::cons_(std::move(x),
                                                                std::move(xs));
                       }},
            l->v());
      }
    }();
  } else {
    unsigned int n_ = n - 1;
    return [&](void) {
      if (((std::move(l).use_count() == 1) &&
           (std::move(l)->v().index() == 1))) {
        auto &_rf = std::get<1>(std::move(l)->v_mut());
        unsigned int y = std::move(_rf._a0);
        std::shared_ptr<List<unsigned int>> ys = std::move(_rf._a1);
        _rf._a0 = std::move(y);
        _rf._a1 = update_nth(n_, x, std::move(ys));
        return std::move(l);
      } else {
        return std::visit(
            Overloaded{[&](const typename List<unsigned int>::nil _args)
                           -> std::shared_ptr<List<unsigned int>> {
                         return std::move(l);
                       },
                       [&](const typename List<unsigned int>::cons _args)
                           -> std::shared_ptr<List<unsigned int>> {
                         unsigned int y = _args._a0;
                         std::shared_ptr<List<unsigned int>> ys = _args._a1;
                         return List<unsigned int>::ctor::cons_(
                             std::move(y),
                             update_nth(std::move(n_), x, std::move(ys)));
                       }},
            std::move(l)->v());
      }
    }();
  }
}

std::shared_ptr<LoadProgramHeadWrite::state>
LoadProgramHeadWrite::set_prom_params(
    std::shared_ptr<LoadProgramHeadWrite::state> s, const unsigned int addr,
    const unsigned int data, const bool enable) {
  return std::make_shared<LoadProgramHeadWrite::state>(state{
      std::move(s)->rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<LoadProgramHeadWrite::state> LoadProgramHeadWrite::execute_wpm(
    std::shared_ptr<LoadProgramHeadWrite::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<LoadProgramHeadWrite::state>(
      state{std::move(new_rom), s->prom_addr, s->prom_data, s->prom_enable});
}

std::shared_ptr<LoadProgramHeadWrite::state> LoadProgramHeadWrite::load_program(
    std::shared_ptr<LoadProgramHeadWrite::state> s, const unsigned int base,
    const std::shared_ptr<List<unsigned int>> &bytes) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::nil _args)
                     -> std::shared_ptr<LoadProgramHeadWrite::state> {
                   return std::move(s);
                 },
                 [&](const typename List<unsigned int>::cons _args)
                     -> std::shared_ptr<LoadProgramHeadWrite::state> {
                   unsigned int b = _args._a0;
                   std::shared_ptr<List<unsigned int>> rest = _args._a1;
                   std::shared_ptr<LoadProgramHeadWrite::state> s1 =
                       set_prom_params(std::move(s), base, std::move(b), true);
                   std::shared_ptr<LoadProgramHeadWrite::state> s2 =
                       execute_wpm(std::move(s1));
                   return load_program(std::move(s2), ((base + 1u) % 4096u),
                                       std::move(rest));
                 }},
      bytes->v());
}
