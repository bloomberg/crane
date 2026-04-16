#include <ram_init_reset.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<RamInitReset::state>
RamInitReset::reset_state(const std::shared_ptr<RamInitReset::state> &s) {
  return std::make_shared<RamInitReset::state>(
      state{s->state_regs, 0u, false, 0u, List<unsigned int>::nil(),
            s->state_ram, default_sel, s->state_rom});
}

__attribute__((pure))
std::pair<std::optional<unsigned int>, std::shared_ptr<RamInitReset::state>>
RamInitReset::pop_stack(std::shared_ptr<RamInitReset::state> s) {
  auto &&_sv = s->state_stack;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return std::make_pair(std::optional<unsigned int>(), std::move(s));
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv->v());
    return std::make_pair(
        std::make_optional<unsigned int>(d_a0),
        std::make_shared<RamInitReset::state>(
            state{s->state_regs, s->state_acc, s->state_carry, s->state_pc,
                  d_a1, s->state_ram, s->state_sel, s->state_rom}));
  }
}
