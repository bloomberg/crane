#include <superfluous_moves.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Identity tick so the reproducer stays minimal while keeping the same shape.
__attribute__((pure)) SuperfluousMoves::game_state
SuperfluousMoves::tick(SuperfluousMoves::game_state gs) {
  return gs;
}

/// Life loss used to create the branch-local gs3 value.
__attribute__((pure)) SuperfluousMoves::game_state
SuperfluousMoves::lose_one_life(const SuperfluousMoves::game_state &gs) {
  return game_state{position{9u}, gs.ghosts,
                    (gs.lives ? gs.lives - 1 : gs.lives)};
}

/// Reduced branch reproducer without the outer option * nat wrapper.
__attribute__((pure)) std::pair<bool, SuperfluousMoves::loop_state>
SuperfluousMoves::bad_branch(SuperfluousMoves::loop_state ls) {
  SuperfluousMoves::game_state gs1 = ls.ls_game;
  bool do_tick = true;
  SuperfluousMoves::game_state gs2;
  if (do_tick) {
    gs2 = tick(gs1);
  } else {
    gs2 = gs1;
  }
  switch (forced_mode) {
  case Mode::e_CHASE: {
    SuperfluousMoves::game_state gs3 = lose_one_life(gs2);
    if (gs3.lives == 0u) {
      return std::make_pair(false, loop_state{gs3, gs3.pacpos, gs3.ghosts});
    } else {
      return std::make_pair(false, loop_state{gs3, gs3.pacpos, gs3.ghosts});
    }
  }
  case Mode::e_FRIGHTENED: {
    return std::make_pair(false, ls);
  }
  default:
    std::unreachable();
  }
}
