#include <superfluous_moves.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Identity tick so the reproducer stays minimal while keeping the same shape.
std::shared_ptr<SuperfluousMoves::game_state>
SuperfluousMoves::tick(std::shared_ptr<SuperfluousMoves::game_state> gs) {
  return std::move(gs);
}

/// Life loss used to create the branch-local gs3 value.
std::shared_ptr<SuperfluousMoves::game_state> SuperfluousMoves::lose_one_life(
    std::shared_ptr<SuperfluousMoves::game_state> gs) {
  return std::make_shared<SuperfluousMoves::game_state>(
      game_state{std::make_shared<SuperfluousMoves::position>(position{9u}),
                 gs->ghosts, (gs->lives ? gs->lives - 1 : gs->lives)});
}

/// Reduced branch reproducer without the outer option * nat wrapper.
__attribute__((pure))
std::pair<bool, std::shared_ptr<SuperfluousMoves::loop_state>>
SuperfluousMoves::bad_branch(std::shared_ptr<SuperfluousMoves::loop_state> ls) {
  std::shared_ptr<SuperfluousMoves::game_state> gs1 = ls->ls_game;
  bool do_tick = true;
  std::shared_ptr<SuperfluousMoves::game_state> gs2;
  if (do_tick) {
    gs2 = tick(std::move(gs1));
  } else {
    gs2 = std::move(gs1);
  }
  switch (forced_mode) {
  case Mode::e_CHASE: {
    std::shared_ptr<SuperfluousMoves::game_state> gs3 =
        lose_one_life(std::move(gs2));
    if (gs3->lives == 0u) {
      return std::make_pair(false,
                            std::make_shared<SuperfluousMoves::loop_state>(
                                loop_state{gs3, gs3->pacpos, gs3->ghosts}));
    } else {
      return std::make_pair(false,
                            std::make_shared<SuperfluousMoves::loop_state>(
                                loop_state{gs3, gs3->pacpos, gs3->ghosts}));
    }
  }
  case Mode::e_FRIGHTENED: {
    return std::make_pair(false, ls);
  }
  default:
    std::unreachable();
  }
}
