#include <crane_move_hunt.h>

#include <memory>
#include <toy_helpers.h>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<CraneMoveHunt::box>
CraneMoveHunt::clone_box(std::shared_ptr<CraneMoveHunt::box> b) {
  return std::make_shared<CraneMoveHunt::box>(box{b->payload, b->enabled});
}

std::shared_ptr<CraneMoveHunt::box>
CraneMoveHunt::keep_box(std::shared_ptr<CraneMoveHunt::box> b) {
  return b;
}

__attribute__((pure)) unsigned int
CraneMoveHunt::use_state(const std::shared_ptr<CraneMoveHunt::state> &s) {
  return (s->core->payload + s->cursor->payload);
}

std::shared_ptr<CraneMoveHunt::state>
CraneMoveHunt::render_state(std::shared_ptr<CraneMoveHunt::state> s) {
  return std::make_shared<CraneMoveHunt::state>(
      state{s->core, s->cursor, s->visible});
}

__attribute__((pure)) unsigned int
CraneMoveHunt::sound_state(const std::shared_ptr<CraneMoveHunt::state> &before,
                           const std::shared_ptr<CraneMoveHunt::state> &after) {
  return (use_state(before) + use_state(after));
}

std::shared_ptr<CraneMoveHunt::state>
CraneMoveHunt::resolve_state(std::shared_ptr<CraneMoveHunt::state> s) {
  return std::make_shared<CraneMoveHunt::state>(
      state{clone_box(s->core), s->cursor, s->visible});
}

__attribute__((pure)) std::pair<bool, std::shared_ptr<CraneMoveHunt::state>>
CraneMoveHunt::handle_state(std::shared_ptr<CraneMoveHunt::state> s) {
  return std::make_pair(s->visible, render_state(s));
}

std::shared_ptr<CraneMoveHunt::box>
CraneMoveHunt::record_function(const std::shared_ptr<CraneMoveHunt::box> &b0) {
  std::shared_ptr<CraneMoveHunt::box> b = keep_box(b0);
  std::shared_ptr<CraneMoveHunt::box> b1 = clone_box(b);
  std::shared_ptr<CraneMoveHunt::box> b2 = clone_box(b);
  if (keep_box(b)->enabled) {
    if (std::move(b)->enabled) {
      return b2;
    } else {
      return b1;
    }
  } else {
    return b1;
  }
}

std::shared_ptr<CraneMoveHunt::state>
CraneMoveHunt::state_function(const std::shared_ptr<CraneMoveHunt::state> &s0) {
  std::shared_ptr<CraneMoveHunt::state> s1 = render_state(s0);
  std::shared_ptr<CraneMoveHunt::state> s2 = resolve_state(std::move(s1));
  return render_state(std::move(s2));
}

std::shared_ptr<CraneMoveHunt::state>
CraneMoveHunt::match_reuse(const std::shared_ptr<CraneMoveHunt::state> &s0) {
  std::shared_ptr<CraneMoveHunt::state> s1 = render_state(s0);
  if (s1->visible) {
    std::shared_ptr<CraneMoveHunt::state> s2 = resolve_state(s1);
    if (s1->visible) {
      return s2;
    } else {
      return s1;
    }
  } else {
    return s1;
  }
}

void tick(std::shared_ptr<CraneMoveHunt::state> s) {
  {
    toy_tick(s);
    return;
  }
}

std::shared_ptr<CraneMoveHunt::state>
effect_frame(const std::shared_ptr<CraneMoveHunt::state> &s0) {
  std::shared_ptr<CraneMoveHunt::state> s1 = CraneMoveHunt::render_state(s0);
  tick(s1);
  tick(s1);
  std::shared_ptr<CraneMoveHunt::state> s2 = CraneMoveHunt::resolve_state(s1);
  tick(s1);
  tick(s2);
  return s2;
}

std::shared_ptr<CraneMoveHunt::state>
effect_pair_frame(const std::shared_ptr<CraneMoveHunt::state> &s0) {
  std::pair<bool, std::shared_ptr<CraneMoveHunt::state>> handled =
      CraneMoveHunt::handle_state(s0);
  bool quit = handled.first;
  std::shared_ptr<CraneMoveHunt::state> s1 = handled.second;
  tick(s1);
  tick(s1);
  std::shared_ptr<CraneMoveHunt::state> s2 = CraneMoveHunt::resolve_state(s1);
  tick(s1);
  tick(s2);
  if (quit) {
    return s2;
  } else {
    return s1;
  }
}

std::shared_ptr<CraneMoveHunt::state>
pure_pair_frame(const std::shared_ptr<CraneMoveHunt::state> &s0) {
  std::pair<bool, std::shared_ptr<CraneMoveHunt::state>> handled =
      CraneMoveHunt::handle_state(s0);
  bool quit = handled.first;
  std::shared_ptr<CraneMoveHunt::state> s1 = handled.second;
  std::shared_ptr<CraneMoveHunt::state> s2 = CraneMoveHunt::resolve_state(s1);
  std::shared_ptr<CraneMoveHunt::state> s3 = CraneMoveHunt::render_state(s1);
  if (quit) {
    return s2;
  } else {
    return s3;
  }
}

std::shared_ptr<CraneMoveHunt::state> exported_effect_frame() {
  return effect_frame(CraneMoveHunt::initial_state);
}

std::shared_ptr<CraneMoveHunt::state> exported_effect_pair_frame() {
  return effect_pair_frame(CraneMoveHunt::initial_state);
}

std::shared_ptr<CraneMoveHunt::state>
axiom_pair_frame(const std::shared_ptr<CraneMoveHunt::state> &s0) {
  std::pair<bool, std::shared_ptr<CraneMoveHunt::state>> handled =
      CraneMoveHunt::handle_state(s0);
  bool quit = handled.first;
  std::shared_ptr<CraneMoveHunt::state> s1 = handled.second;
  std::shared_ptr<CraneMoveHunt::state> s2 = CraneMoveHunt::resolve_state(s1);
  if (quit) {
    return s2;
  } else {
    return s1;
  }
}

std::shared_ptr<CraneMoveHunt::state>
axiom_nat_pair_frame(const std::shared_ptr<CraneMoveHunt::state> &s0) {
  std::pair<bool, std::shared_ptr<CraneMoveHunt::state>> handled =
      CraneMoveHunt::handle_state(s0);
  bool quit = handled.first;
  std::shared_ptr<CraneMoveHunt::state> s1 = handled.second;
  std::shared_ptr<CraneMoveHunt::state> s2 = CraneMoveHunt::resolve_state(s1);
  unsigned int n = toy_tick_nat(s1);
  if ((quit || n == 0u)) {
    return s2;
  } else {
    return s1;
  }
}
