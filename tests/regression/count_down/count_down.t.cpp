#include <count_down.h>

#include <cassert>
#include <iostream>
#include <sstream>

// Helper: capture stdout during a call, return what was printed
template <typename F>
std::string capture_stdout(F f) {
  std::ostringstream captured;
  auto old = std::cout.rdbuf(captured.rdbuf());
  f();
  std::cout.rdbuf(old);
  return captured.str();
}

// Helper: capture stdout with faked stdin
template <typename F>
std::string capture_with_input(const std::string& input, F f) {
  std::istringstream fake_in(input);
  auto old_cin = std::cin.rdbuf(fake_in.rdbuf());
  auto result = capture_stdout(f);
  std::cin.rdbuf(old_cin);
  return result;
}

int main() {
  // ── Fixpoint versions (nat-decreasing) ──

  // count_down: single effect ;; recurse
  assert(capture_stdout([] { CountDown::count_down(3); })
         == "tick\ntick\ntick\n");
  assert(capture_stdout([] { CountDown::count_down(0); }).empty());

  // two_prints: two effects ;; recurse
  assert(capture_stdout([] { CountDown::two_prints(2); })
         == "step 2\n---\nstep 1\n---\n");
  assert(capture_stdout([] { CountDown::two_prints(0); }).empty());

  // echo_loop: get_line ;; print ;; recurse
  assert(capture_with_input("hello\nworld\n",
                            [] { CountDown::echo_loop(2); })
         == "echo: hello\necho: world\n");
  assert(capture_stdout([] { CountDown::echo_loop(0); }).empty());

  // announce: effect in both branches
  assert(capture_stdout([] { CountDown::announce(2); })
         == "counting 2\ncounting 1\ndone\n");
  assert(capture_stdout([] { CountDown::announce(0); }) == "done\n");

  // repeat_msg: multiple arguments, recurse on first
  assert(capture_stdout([] { CountDown::repeat_msg(3, "hi"); })
         == "hi\nhi\nhi\n");
  assert(capture_stdout([] { CountDown::repeat_msg(0, "hi"); }).empty());

  // ── CoFixpoint versions (condition-terminating) ──

  // co_count_down: single effect, stop on "stop"
  assert(capture_with_input("go\ngo\nstop\n",
                            [] { CountDown::co_count_down(); })
         == "tick\ntick\n");
  // immediate stop
  assert(capture_with_input("stop\n",
                            [] { CountDown::co_count_down(); }).empty());

  // co_two_prints: two effects per iteration
  assert(capture_with_input("a\nb\nstop\n",
                            [] { CountDown::co_two_prints(); })
         == "got: a\n---\ngot: b\n---\n");

  // co_echo_loop: read and echo back
  assert(capture_with_input("hello\nworld\nquit\n",
                            [] { CountDown::co_echo_loop(); })
         == "echo: hello\necho: world\n");

  // co_announce: effect in termination branch, round counter
  assert(capture_with_input("go\ngo\nstop\n",
                            [] { CountDown::co_announce(1); })
         == "round 1\nround 2\ndone\n");
  assert(capture_with_input("stop\n",
                            [] { CountDown::co_announce(1); })
         == "done\n");

  // co_repeat: multiple arguments, constant message
  assert(capture_with_input("a\na\nstop\n",
                            [] { CountDown::co_repeat("yo"); })
         == "yo\nyo\n");

  std::cout << "All count_down tests passed!" << std::endl;
  return 0;
}
