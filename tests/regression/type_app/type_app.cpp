#include <type_app.h>

__attribute__((pure)) TypeApp::list<unsigned int>
TypeApp::map_succ(const TypeApp::list<unsigned int> &_x0) {
  return map<unsigned int, unsigned int>(
      [](const unsigned int &x) { return (x + 1u); }, _x0);
}

__attribute__((pure)) unsigned int
TypeApp::NatMonoid::append(const unsigned int &_x0, const unsigned int &_x1) {
  return (_x0 + _x1);
}
