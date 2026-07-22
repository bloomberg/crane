#include "sigt_leaf_forward_dispatcher.h"

/// All prior attempts wrote the action closure directly at the entry's
/// definition site (my_entry := existT psem (0,[]) ((fun tup => ...), ...)),
/// which Crane always concretizes (the generated lambda's parameter is a
/// concrete pair type, not auto). The REAL grammar table
/// (Parser.v/Defs.v) instead builds every production's predicate/action
/// through a SINGLE shared dispatcher function with one big match over
/// the production id -- e.g. production_action (p : production) :
/// predicate_semty p * action_semty p := match p with ... end -- and only
/// THEN stores existT psem p (production_action p) per entry. This test
/// checks whether routing the action through such a shared dispatcher (one
/// function, many match arms, each returning a differently-typed closure)
/// is what forces Crane to emit a genuinely generic auto-parameterized
/// lambda (hitting crane_erase_fn's buggy generic branch) instead of a
/// concretely-typed one -- which would explain why Newick.h/PPM.h/XML.h
/// still fail after all prior fixes.
bool wrap_string(const std::string &s) { return String::eqb1(s, s); }

bool mk_action(uint64_t n, std::any tup) {
  if (n <= 0) {
    const auto &[v, _x] = std::any_cast<std::pair<std::any, std::any>>(tup);
    return wrap_string(v);
  } else {
    uint64_t _x = n - 1;
    const auto &[v, _x0] = std::any_cast<std::pair<std::any, std::any>>(tup);
    return std::any_cast<uint64_t>(v) < (std::any_cast<uint64_t>(v) + 1);
  }
}

domty garg(uint64_t n) {
  if (n <= 0) {
    return std::make_pair(
        std::string(1, (static_cast<char>(
                           (false ? 1 : 0) | (false ? 2 : 0) | (false ? 4 : 0) |
                           (true ? 8 : 0) | (false ? 16 : 0) | (true ? 32 : 0) |
                           (true ? 64 : 0) | (false ? 128 : 0)))) +
            std::string(
                1, (static_cast<char>((true ? 1 : 0) | (false ? 2 : 0) |
                                      (false ? 4 : 0) | (true ? 8 : 0) |
                                      (false ? 16 : 0) | (true ? 32 : 0) |
                                      (true ? 64 : 0) | (false ? 128 : 0)))) +
            std::string(),
        std::monostate{});
  } else {
    uint64_t _x = n - 1;
    return std::make_pair(UINT64_C(0), std::monostate{});
  }
}

bool run(const SigT<std::pair<uint64_t, List<uint64_t>>,
                    std::pair<std::any, std::any>> &e) {
  const auto &[x0, a1] = e;
  const auto &[n, _x] = x0;
  const auto &[f, _x0] = std::any_cast<std::pair<std::any, std::any>>(a1);
  if (std::any_cast<bool>(
          std::any_cast<std::function<std::any(std::any)>>(f)(garg(n)))) {
    return true;
  } else {
    return false;
  }
}

bool check(std::monostate) { return run(my_entry); }

bool Bool::eqb(bool b1, bool b2) {
  if (b1) {
    if (b2) {
      return true;
    } else {
      return false;
    }
  } else {
    if (b2) {
      return false;
    } else {
      return true;
    }
  }
}

bool Ascii::eqb0(char a, char b) {
  bool a0 = a & 1;
  bool a1 = (a >> 1) & 1;
  bool a2 = (a >> 2) & 1;
  bool a3 = (a >> 3) & 1;
  bool a4 = (a >> 4) & 1;
  bool a5 = (a >> 5) & 1;
  bool a6 = (a >> 6) & 1;
  bool a7 = (a >> 7) & 1;
  bool b0 = b & 1;
  bool b1 = (b >> 1) & 1;
  bool b2 = (b >> 2) & 1;
  bool b3 = (b >> 3) & 1;
  bool b4 = (b >> 4) & 1;
  bool b5 = (b >> 5) & 1;
  bool b6 = (b >> 6) & 1;
  bool b7 = (b >> 7) & 1;
  if (((((((Bool::eqb(a0, b0) ? Bool::eqb(a1, b1) : false) ? Bool::eqb(a2, b2)
                                                           : false)
              ? Bool::eqb(a3, b3)
              : false)
             ? Bool::eqb(a4, b4)
             : false)
            ? Bool::eqb(a5, b5)
            : false)
           ? Bool::eqb(a6, b6)
           : false)) {
    return Bool::eqb(a7, b7);
  } else {
    return false;
  }
}

bool String::eqb1(const std::string &s1, const std::string &s2) {
  if (s1.empty()) {
    if (s2.empty()) {
      return true;
    } else {
      char _x = s2[0];
      std::string _x0 = s2.substr(1);
      return false;
    }
  } else {
    char c1 = s1[0];
    std::string s1_ = s1.substr(1);
    if (s2.empty()) {
      return false;
    } else {
      char c2 = s2[0];
      std::string s2_ = s2.substr(1);
      if (Ascii::eqb0(c1, c2)) {
        return String::eqb1(s1_, s2_);
      } else {
        return false;
      }
    }
  }
}
