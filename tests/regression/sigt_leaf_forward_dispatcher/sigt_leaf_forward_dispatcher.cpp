#include "sigt_leaf_forward_dispatcher.h"

/// Unlike sigt_leaf_forward_topfn, which writes the action closure directly
/// at the entry's definition site, this test routes the action through a
/// SINGLE shared dispatcher function (mk_action) with one match over the
/// production id -- the shape of the REAL grammar table (Parser.v/Defs.v),
/// which builds every production's predicate/action via
/// production_action (p : production) : predicate_semty p * action_semty p :=
/// match p with ... end and only then stores existT psem p
/// (production_action p) per entry.
///
/// The consumer of the dispatched closure (run, via mk_action) is generic
/// over the runtime-varying index n, so it must read the closure's domain
/// (domty n, a value-dependent alias) through the fully-erased
/// representation any_cast<pair<any,any>>.  This forced two fixes: the
/// producer (garg) must DEEP-erase the pair components it returns into the
/// value-dependent std::any slot (so the stored value is pair<any,any>,
/// not pair<string,unit>), and the pair_wrap/fst/snd accessors must
/// not synthesize out-of-scope template parameters when casting an erased
/// field.  Both producer and consumer now agree on the deep-erased
/// representation.
bool wrap_string(const std::string &s) { return String::eqb1(s, s); }

bool mk_action(uint64_t n, std::any tup) {
  if (n <= 0) {
    const auto &[v, _x] = std::any_cast<std::pair<std::any, std::any>>(tup);
    return wrap_string(std::any_cast<std::string>(v));
  } else {
    uint64_t _x = n - 1;
    const auto &[v, _x0] = std::any_cast<std::pair<std::any, std::any>>(tup);
    return std::any_cast<uint64_t>(v) < (std::any_cast<uint64_t>(v) + 1);
  }
}

domty garg(uint64_t n) {
  if (n <= 0) {
    return std::make_pair(
        std::any(std::string(1, (static_cast<char>(
                                    (false ? 1 : 0) | (false ? 2 : 0) |
                                    (false ? 4 : 0) | (true ? 8 : 0) |
                                    (false ? 16 : 0) | (true ? 32 : 0) |
                                    (true ? 64 : 0) | (false ? 128 : 0)))) +
                 std::string(1, (static_cast<char>(
                                    (true ? 1 : 0) | (false ? 2 : 0) |
                                    (false ? 4 : 0) | (true ? 8 : 0) |
                                    (false ? 16 : 0) | (true ? 32 : 0) |
                                    (true ? 64 : 0) | (false ? 128 : 0)))) +
                 std::string()),
        std::any(std::monostate{}));
  } else {
    uint64_t _x = n - 1;
    return std::make_pair(std::any(UINT64_C(0)), std::any(std::monostate{}));
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
