#ifndef INCLUDED_APP_DOUBLECALL
#define INCLUDED_APP_DOUBLECALL

#include <deque>

struct AppDoublecall {
  /// A fixpoint function that returns a list -- when used as the second
  /// argument to (++) it becomes the %a1 function-call expression in the
  /// generated template, causing the double evaluation.
  static std::deque<uint64_t> gen_list(uint64_t n);
  /// When extracted, the (++) here uses the Datatypes.app template.
  /// gen_list a and gen_list b are both function calls, so the template
  /// substitutes gen_list(b) twice:
  /// auto _r = gen_list(a);
  /// _r.insert(_r.end(), gen_list(b).begin(), gen_list(b).end());  (* BUG *)
  static std::deque<uint64_t> concat_two(uint64_t a, uint64_t b);
};

#endif // INCLUDED_APP_DOUBLECALL
