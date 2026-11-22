#include <bake_alternating_types_quadratic.h>

#include <sys/resource.h>

#include <cassert>
#include <iostream>

int main() {
  // The baked constant is read at static initialisation, before main.
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  double user = static_cast<double>(ru.ru_utime.tv_sec) +
                static_cast<double>(ru.ru_utime.tv_usec) / 1e6;
  auto r = BakeAlternatingTypesQuadratic::result;
  std::cout << "result = " << r << ", user CPU before main = " << user << " s"
            << std::endl;
  assert(r == 50000);
  assert(user < 1.0);
  return 0;
}
