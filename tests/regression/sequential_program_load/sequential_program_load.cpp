#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <sequential_program_load.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> SequentialProgramLoad::rom_(
    const std::shared_ptr<SequentialProgramLoad::state> &s) {
  return s->rom_;
}

unsigned int SequentialProgramLoad::ptr_(
    const std::shared_ptr<SequentialProgramLoad::state> &s) {
  return s->ptr_;
}

std::shared_ptr<SequentialProgramLoad::state> SequentialProgramLoad::write_byte(
    std::shared_ptr<SequentialProgramLoad::state> s, const unsigned int b) {
  return std::make_shared<SequentialProgramLoad::state>(state{
      update_nth<unsigned int>(s->ptr_, std::move(b), s->rom_), (s->ptr_ + 1)});
}

std::shared_ptr<SequentialProgramLoad::state>
SequentialProgramLoad::load_program(
    std::shared_ptr<SequentialProgramLoad::state> s,
    const std::shared_ptr<List<unsigned int>> &bytes) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::nil _args)
                     -> std::shared_ptr<SequentialProgramLoad::state> {
                   return std::move(s);
                 },
                 [&](const typename List<unsigned int>::cons _args)
                     -> std::shared_ptr<SequentialProgramLoad::state> {
                   unsigned int b = _args._a0;
                   std::shared_ptr<List<unsigned int>> rest = _args._a1;
                   return load_program(write_byte(std::move(s), std::move(b)),
                                       std::move(rest));
                 }},
      bytes->v());
}
