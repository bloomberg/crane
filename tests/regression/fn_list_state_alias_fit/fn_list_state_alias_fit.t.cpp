#include <fn_list_state_alias_fit.h>
#include <iostream>
int main() {
  std::cout << FnListStateAliasFit::result << std::endl;
  return FnListStateAliasFit::result == 705 ? 0 : 1;
}
