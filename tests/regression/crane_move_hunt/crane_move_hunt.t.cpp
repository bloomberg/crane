#include <crane_move_hunt.h>

#include <cassert>
#include <iostream>

int main() {
  // record_constant: keep_box + clone_box reuse of same binding
  auto r1 = exported_record_constant;
  std::cout << "record_constant.payload = " << r1->payload << std::endl;
  assert(r1->payload == 41u);
  assert(r1->enabled == true);

  // record_function: same pattern as above but through a function
  auto r2 = exported_record_function;
  std::cout << "record_function.payload = " << r2->payload << std::endl;
  assert(r2->payload == 41u);
  assert(r2->enabled == true);

  // state_constant: chained render/resolve/sound on same state bindings
  auto s1 = exported_state_constant;
  std::cout << "state_constant.core.payload = " << s1->core->payload << std::endl;
  assert(s1->core->payload == 41u);

  // state_function: same chain through a function parameter
  auto s2 = exported_state_function;
  std::cout << "state_function.core.payload = " << s2->core->payload << std::endl;
  assert(s2->core->payload == 41u);

  // match_reuse: state reused across match branches
  auto s3 = exported_match_reuse;
  std::cout << "match_reuse.core.payload = " << s3->core->payload << std::endl;
  assert(s3->core->payload == 41u);

  // effect_frame: itree with multiple ticks reusing same state
  // BUG: generated code moves s1 into resolve_state then ticks moved-from s1
  auto ef = exported_effect_frame();
  std::cout << "effect_frame.core.payload = " << ef->core->payload << std::endl;
  assert(ef->core->payload == 41u);

  // effect_pair_frame: pair destructuring + itree reuse
  auto epf = exported_effect_pair_frame();
  std::cout << "effect_pair_frame.core.payload = " << epf->core->payload << std::endl;
  assert(epf->core->payload == 41u);

  // pure_pair_frame: pair destructuring, pure version
  auto ppf = exported_pure_pair_frame;
  std::cout << "pure_pair_frame.core.payload = " << ppf->core->payload << std::endl;
  assert(ppf->core->payload == 41u);

  // axiom_pair_frame: axiom-based tick + pair destructuring
  auto apf = exported_axiom_pair_frame;
  std::cout << "axiom_pair_frame.core.payload = " << apf->core->payload << std::endl;
  assert(apf->core->payload == 41u);

  // axiom_nat_pair_frame: axiom returning nat + pair destructuring
  auto anpf = exported_axiom_nat_pair_frame;
  std::cout << "axiom_nat_pair_frame.core.payload = " << anpf->core->payload << std::endl;
  assert(anpf->core->payload == 41u);

  std::cout << "All crane_move_hunt tests passed!" << std::endl;
  return 0;
}
