// Rocq bug #7228: extraction with conservative types and dependent match
// The bug involved extracting a dependent match where the return type
// depends on the scrutinee (match d return t_of d with ...).
//
// Bug status in Crane: NOT REPLICATED. Extraction and compilation succeed.

#include <rocq_bug_7228.h>

int main() {
  // Compilation check - dependent return types are tricky for extraction
  return 0;
}
