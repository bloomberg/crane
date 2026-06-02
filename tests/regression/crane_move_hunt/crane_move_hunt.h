#ifndef INCLUDED_CRANE_MOVE_HUNT
#define INCLUDED_CRANE_MOVE_HUNT

#include <toy_helpers.h>
#include <utility>
#include <variant>

struct CraneMoveHunt {
  struct box {
    uint64_t payload;
    bool enabled;
  };

  struct state {
    box core;
    box cursor;
    bool visible;
  };

  static box clone_box(const box &b);
  static box keep_box(box b);
  static uint64_t use_state(const state &s);
  static state render_state(const state &s);
  static uint64_t sound_state(const state &before, const state &after);
  static state resolve_state(const state &s);
  static std::pair<bool, state> handle_state(const state &s);
  static inline const box initial_box = box{UINT64_C(41), true};
  static inline const box other_box = box{UINT64_C(1), false};
  static inline const state initial_state = state{initial_box, other_box, true};
  static inline const box record_constant = []() {
    box b = keep_box(initial_box);
    box b1 = clone_box(b);
    box b2 = clone_box(b);
    if (keep_box(b).enabled) {
      if (std::move(b).enabled) {
        return b2;
      } else {
        return b1;
      }
    } else {
      return b1;
    }
  }();
  static box record_function(const box &b0);
  static inline const state state_constant = []() {
    state s1 = render_state(initial_state);
    state s2 = resolve_state(std::move(s1));
    return render_state(std::move(s2));
  }();
  static state state_function(const state &s0);
  static state match_reuse(const state &s0);
};

void tick(CraneMoveHunt::state s);
CraneMoveHunt::state effect_frame(const CraneMoveHunt::state &s0);
CraneMoveHunt::state effect_pair_frame(const CraneMoveHunt::state &s0);
CraneMoveHunt::state pure_pair_frame(const CraneMoveHunt::state &s0);
const CraneMoveHunt::box exported_record_constant =
    CraneMoveHunt::record_constant;
const CraneMoveHunt::box exported_record_function =
    CraneMoveHunt::record_function(CraneMoveHunt::initial_box);
const CraneMoveHunt::state exported_state_constant =
    CraneMoveHunt::state_constant;
const CraneMoveHunt::state exported_state_function =
    CraneMoveHunt::state_function(CraneMoveHunt::initial_state);
const CraneMoveHunt::state exported_match_reuse =
    CraneMoveHunt::match_reuse(CraneMoveHunt::initial_state);
CraneMoveHunt::state exported_effect_frame();
CraneMoveHunt::state exported_effect_pair_frame();
const CraneMoveHunt::state exported_pure_pair_frame =
    pure_pair_frame(CraneMoveHunt::initial_state);
CraneMoveHunt::state axiom_pair_frame(const CraneMoveHunt::state &s0);
const CraneMoveHunt::state exported_axiom_pair_frame =
    axiom_pair_frame(CraneMoveHunt::initial_state);
CraneMoveHunt::state axiom_nat_pair_frame(const CraneMoveHunt::state &s0);
const CraneMoveHunt::state exported_axiom_nat_pair_frame =
    axiom_nat_pair_frame(CraneMoveHunt::initial_state);

#endif // INCLUDED_CRANE_MOVE_HUNT
