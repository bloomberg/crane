#include "superfluous_moves.h"

SuperfluousMoves::game_state
SuperfluousMoves::tick(SuperfluousMoves::game_state gs) {
  return gs;
}

SuperfluousMoves::game_state
SuperfluousMoves::lose_one_life(const SuperfluousMoves::game_state &gs) {
  return game_state{position{UINT64_C(9)}, gs.ghosts,
                    (gs.lives ? gs.lives - 1 : gs.lives)};
}

std::pair<bool, SuperfluousMoves::loop_state>
SuperfluousMoves::bad_branch(SuperfluousMoves::loop_state ls) {
  const SuperfluousMoves::game_state &gs1 = ls.ls_game;
  bool do_tick = true;
  SuperfluousMoves::game_state gs2;
  if (do_tick) {
    gs2 = tick(gs1);
  } else {
    gs2 = gs1;
  }
  switch (forced_mode) {
  case Mode::CHASE: {
    SuperfluousMoves::game_state gs3 = lose_one_life(std::move(gs2));
    if (gs3.lives == UINT64_C(0)) {
      return std::make_pair(false, loop_state{gs3, gs3.pacpos, gs3.ghosts});
    } else {
      return std::make_pair(false, loop_state{gs3, gs3.pacpos, gs3.ghosts});
    }
    break;
  }
  case Mode::FRIGHTENED: {
    return std::make_pair(false, std::move(ls));
  }
  default:
    std::unreachable();
  }
}
