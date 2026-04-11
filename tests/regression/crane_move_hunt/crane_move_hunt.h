#ifndef INCLUDED_CRANE_MOVE_HUNT
#define INCLUDED_CRANE_MOVE_HUNT

#include <memory>
#include <toy_helpers.h>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct CraneMoveHunt {
  struct box {
    unsigned int payload;
    bool enabled;
  };

  struct state {
    std::shared_ptr<box> core;
    std::shared_ptr<box> cursor;
    bool visible;
  };

  static std::shared_ptr<box> clone_box(std::shared_ptr<box> b);
  static std::shared_ptr<box> keep_box(std::shared_ptr<box> b);
  __attribute__((pure)) static unsigned int
  use_state(const std::shared_ptr<state> &s);
  static std::shared_ptr<state> render_state(std::shared_ptr<state> s);
  __attribute__((pure)) static unsigned int
  sound_state(const std::shared_ptr<state> &before,
              const std::shared_ptr<state> &after);
  static std::shared_ptr<state> resolve_state(std::shared_ptr<state> s);
  __attribute__((pure)) static std::pair<bool, std::shared_ptr<state>>
  handle_state(std::shared_ptr<state> s);
  static inline const std::shared_ptr<box> initial_box =
      std::make_shared<box>(box{41u, true});
  static inline const std::shared_ptr<box> other_box =
      std::make_shared<box>(box{1u, false});
  static inline const std::shared_ptr<state> initial_state =
      std::make_shared<state>(state{initial_box, other_box, true});
  static inline const std::shared_ptr<box> record_constant = []() {
    std::shared_ptr<box> b = keep_box(initial_box);
    std::shared_ptr<box> b1 = clone_box(b);
    std::shared_ptr<box> b2 = clone_box(b);
    if (keep_box(b)->enabled) {
      if (std::move(b)->enabled) {
        return std::move(b2);
      } else {
        return std::move(b1);
      }
    } else {
      return std::move(b1);
    }
  }();
  static std::shared_ptr<box> record_function(const std::shared_ptr<box> &b0);
  static inline const std::shared_ptr<state> state_constant = []() {
    std::shared_ptr<state> s1 = render_state(initial_state);
    std::shared_ptr<state> s2 = resolve_state(std::move(s1));
    return render_state(std::move(s2));
  }();
  static std::shared_ptr<state>
  state_function(const std::shared_ptr<state> &s0);
  static std::shared_ptr<state> match_reuse(const std::shared_ptr<state> &s0);
};

void tick(std::shared_ptr<CraneMoveHunt::state> s);
std::shared_ptr<CraneMoveHunt::state>
effect_frame(const std::shared_ptr<CraneMoveHunt::state> &s0);
std::shared_ptr<CraneMoveHunt::state>
effect_pair_frame(const std::shared_ptr<CraneMoveHunt::state> &s0);
std::shared_ptr<CraneMoveHunt::state>
pure_pair_frame(const std::shared_ptr<CraneMoveHunt::state> &s0);
const std::shared_ptr<CraneMoveHunt::box> exported_record_constant =
    CraneMoveHunt::record_constant;
const std::shared_ptr<CraneMoveHunt::box> exported_record_function =
    CraneMoveHunt::record_function(CraneMoveHunt::initial_box);
const std::shared_ptr<CraneMoveHunt::state> exported_state_constant =
    CraneMoveHunt::state_constant;
const std::shared_ptr<CraneMoveHunt::state> exported_state_function =
    CraneMoveHunt::state_function(CraneMoveHunt::initial_state);
const std::shared_ptr<CraneMoveHunt::state> exported_match_reuse =
    CraneMoveHunt::match_reuse(CraneMoveHunt::initial_state);
std::shared_ptr<CraneMoveHunt::state> exported_effect_frame();
std::shared_ptr<CraneMoveHunt::state> exported_effect_pair_frame();
const std::shared_ptr<CraneMoveHunt::state> exported_pure_pair_frame =
    pure_pair_frame(CraneMoveHunt::initial_state);
std::shared_ptr<CraneMoveHunt::state>
axiom_pair_frame(const std::shared_ptr<CraneMoveHunt::state> &s0);
const std::shared_ptr<CraneMoveHunt::state> exported_axiom_pair_frame =
    axiom_pair_frame(CraneMoveHunt::initial_state);
std::shared_ptr<CraneMoveHunt::state>
axiom_nat_pair_frame(const std::shared_ptr<CraneMoveHunt::state> &s0);
const std::shared_ptr<CraneMoveHunt::state> exported_axiom_nat_pair_frame =
    axiom_nat_pair_frame(CraneMoveHunt::initial_state);

#endif // INCLUDED_CRANE_MOVE_HUNT
