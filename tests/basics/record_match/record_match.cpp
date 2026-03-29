#include <record_match.h>

#include <memory>
#include <type_traits>

__attribute__((pure)) unsigned int
RecordMatch::sum(const std::shared_ptr<RecordMatch::MyRec> &r) {
  return [&](void) {
    unsigned int n1 = r->f1;
    unsigned int n2 = r->f2;
    unsigned int n3 = r->f3;
    return ((n1 + n2) + n3);
  }();
}
