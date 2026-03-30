#include <itree_effects.h>

#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// ------------------------------------------------------------------
void ITreeEffects::greet() {
  (void)0 /* log: "starting greet"s */;
  std::cout << "What is your name?"s << '\n';
  std::string name = []() -> std::string {
    std::string s;
    std::getline(std::cin, s);
    return s;
  }();
  std::cout << name << '\n';
  (void)0 /* log: "finished greet"s */;
  return;
}

void ITreeEffects::simple_log() {
  (void)0 /* log: "hello"s */;
  (void)0 /* log: "world"s */;
  return;
}

void ITreeEffects::simple_print() {
  std::cout << "line1"s << '\n';
  std::cout << "line2"s << '\n';
  return;
}

std::shared_ptr<Nat> ITreeEffects::pure_value() {
  return Nat::s(Nat::s(Nat::s(Nat::s(
      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(Nat::o()))))))))))))))))))))))))))))))))))))))))));
}
