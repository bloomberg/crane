#include <run_bot_handle_existential.h>

#include <cassert>
#include <iostream>

int main() {
  // prog = Vis (Out zero) (fun _ => Ret 3); run_bot answers Out with tt.
  assert(RunBotHandleExistential::is_three);
  std::cout << "run_bot_handle_existential: ok" << std::endl;
  return 0;
}
