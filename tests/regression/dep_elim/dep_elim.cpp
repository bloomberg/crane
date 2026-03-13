#include <dep_elim.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
DepElim::fin_to_nat(const unsigned int _x,
                    const std::shared_ptr<DepElim::fin> &f) {
  return std::visit(
      Overloaded{[](const typename DepElim::fin::FZ _args) -> unsigned int {
                   return 0u;
                 },
                 [](const typename DepElim::fin::FS _args) -> unsigned int {
                   unsigned int n0 = _args.d_a0;
                   std::shared_ptr<DepElim::fin> f_ = _args.d_a1;
                   return (fin_to_nat(std::move(n0), std::move(f_)) + 1);
                 }},
      f->v());
}

__attribute__((pure)) unsigned int
DepElim::get_present(const std::shared_ptr<DepElim::avail> &a) {
  return std::visit(
      Overloaded{
          [](const typename DepElim::avail::Present _args) -> unsigned int {
            unsigned int n = _args.d_a0;
            return std::move(n);
          },
          [](const typename DepElim::avail::Absent _args) -> unsigned int {
            throw std::logic_error("unreachable");
          }},
      a->v());
}
