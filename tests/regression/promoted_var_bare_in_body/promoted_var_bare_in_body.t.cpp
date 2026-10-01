#include <promoted_var_bare_in_body.h>

#include <cassert>

int main() {
  auto d = PromotedVarBareInBody::run;
  (void)d;
  return 0;
}
