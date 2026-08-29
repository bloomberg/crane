#include "type_app.h"

TypeApp::list<uint64_t> TypeApp::map_succ(const TypeApp::list<uint64_t> &_x0) {
  return map<uint64_t, uint64_t>([](uint64_t x) { return (x + UINT64_C(1)); },
                                 _x0);
}

uint64_t TypeApp::NatMonoid::append(uint64_t _x0, uint64_t _x1) {
  return (_x0 + _x1);
}
