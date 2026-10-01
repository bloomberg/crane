#include <tfunctor_list_of_triples.h>

#include <cassert>
#include <iostream>

int main() {
  // tfmap S over [(1, Phi 2, [Md 5])]: id stays 1, Phi 3.
  assert(TfunctorListOfTriples::is_four);
  std::cout << "tfunctor_list_of_triples: ok" << std::endl;
  return 0;
}
