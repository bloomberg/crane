#include "type_app.h"

TypeApp::list<uint64_t> TypeApp::map_succ(const TypeApp::list<uint64_t> &x0_) {
  return map<uint64_t, uint64_t>([](uint64_t x) { return (x + UINT64_C(1)); },
                                 x0_);
}

uint64_t TypeApp::NatMonoid::append(uint64_t x0_, uint64_t x1_) {
  return (x0_ + x1_);
}
