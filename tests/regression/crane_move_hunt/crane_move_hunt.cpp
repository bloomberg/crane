#include <crane_move_hunt.h>

#include <memory>
#include <optional>
#include <toy_helpers.h>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) CraneMoveHunt::box
CraneMoveHunt::clone_box(const CraneMoveHunt::box &b) {
  return box{b.payload, b.enabled};
}

__attribute__((pure)) CraneMoveHunt::box
CraneMoveHunt::keep_box(CraneMoveHunt::box b) {
  return b;
}

__attribute__((pure)) unsigned int
CraneMoveHunt::use_state(const CraneMoveHunt::state &s) {
  return (s.core.payload + s.cursor.payload);
}

__attribute__((pure)) CraneMoveHunt::state
CraneMoveHunt::render_state(const CraneMoveHunt::state &s) {
  return state{s.core, s.cursor, s.visible};
}

__attribute__((pure)) unsigned int
CraneMoveHunt::sound_state(const CraneMoveHunt::state &before,
                           const CraneMoveHunt::state &after) {
  return (use_state(before) + use_state(after));
}

__attribute__((pure)) CraneMoveHunt::state
CraneMoveHunt::resolve_state(const CraneMoveHunt::state &s) {
  return state{clone_box(s.core), s.cursor, s.visible};
}

__attribute__((pure)) std::pair<bool, CraneMoveHunt::state>
CraneMoveHunt::handle_state(const CraneMoveHunt::state &s) {
  return std::make_pair(s.visible, render_state(s));
}

__attribute__((pure)) CraneMoveHunt::box
CraneMoveHunt::record_function(const CraneMoveHunt::box &b0) {
  CraneMoveHunt::box b = keep_box(b0);
  CraneMoveHunt::box b1 = clone_box(b);
  CraneMoveHunt::box b2 = clone_box(b);
  if (keep_box(b).enabled) {
    if (b.enabled) {
      return b2;
    } else {
      return b1;
    }
  } else {
    return b1;
  }
}

__attribute__((pure)) CraneMoveHunt::state
CraneMoveHunt::state_function(const CraneMoveHunt::state &s0) {
  CraneMoveHunt::state s1 = render_state(s0);
  CraneMoveHunt::state s2 = resolve_state(s1);
  return render_state(s2);
}

__attribute__((pure)) CraneMoveHunt::state
CraneMoveHunt::match_reuse(const CraneMoveHunt::state &s0) {
  CraneMoveHunt::state s1 = render_state(s0);
  if (s1.visible) {
    CraneMoveHunt::state s2 = resolve_state(s1);
    if (s1.visible) {
      return s2;
    } else {
      return s1;
    }
  } else {
    return s1;
  }
}

void tick(CraneMoveHunt::state s) {
  {
    toy_tick(s);
    return;
  }
}

CraneMoveHunt::state effect_frame(const CraneMoveHunt::state &s0) {
  CraneMoveHunt::state s1 = CraneMoveHunt::render_state(s0);
  tick(s1);
  tick(s1);
  CraneMoveHunt::state s2 = CraneMoveHunt::resolve_state(s1);
  tick(s1);
  tick(s2);
  return s2;
}

CraneMoveHunt::state effect_pair_frame(const CraneMoveHunt::state &s0) {
  std::pair<bool, CraneMoveHunt::state> handled =
      CraneMoveHunt::handle_state(s0);
  const bool &quit = handled.first;
  const CraneMoveHunt::state &s1 = handled.second;
  tick(s1);
  tick(s1);
  CraneMoveHunt::state s2 = CraneMoveHunt::resolve_state(s1);
  tick(s1);
  tick(s2);
  if (quit) {
    return s2;
  } else {
    return s1;
  }
}

__attribute__((pure)) CraneMoveHunt::state
pure_pair_frame(const CraneMoveHunt::state &s0) {
  std::pair<bool, CraneMoveHunt::state> handled =
      CraneMoveHunt::handle_state(s0);
  const bool &quit = handled.first;
  const CraneMoveHunt::state &s1 = handled.second;
  CraneMoveHunt::state s2 = CraneMoveHunt::resolve_state(s1);
  CraneMoveHunt::state s3 = CraneMoveHunt::render_state(s1);
  if (quit) {
    return s2;
  } else {
    return s3;
  }
}

CraneMoveHunt::state exported_effect_frame() {
  return effect_frame(CraneMoveHunt::initial_state);
}

CraneMoveHunt::state exported_effect_pair_frame() {
  return effect_pair_frame(CraneMoveHunt::initial_state);
}

__attribute__((pure)) CraneMoveHunt::state
axiom_pair_frame(const CraneMoveHunt::state &s0) {
  std::pair<bool, CraneMoveHunt::state> handled =
      CraneMoveHunt::handle_state(s0);
  const bool &quit = handled.first;
  const CraneMoveHunt::state &s1 = handled.second;
  CraneMoveHunt::state s2 = CraneMoveHunt::resolve_state(s1);
  if (quit) {
    return s2;
  } else {
    return s1;
  }
}

__attribute__((pure)) CraneMoveHunt::state
axiom_nat_pair_frame(const CraneMoveHunt::state &s0) {
  std::pair<bool, CraneMoveHunt::state> handled =
      CraneMoveHunt::handle_state(s0);
  const bool &quit = handled.first;
  const CraneMoveHunt::state &s1 = handled.second;
  CraneMoveHunt::state s2 = CraneMoveHunt::resolve_state(s1);
  unsigned int n = toy_tick_nat(s1);
  if ((quit || n == 0u)) {
    return s2;
  } else {
    return s1;
  }
}
