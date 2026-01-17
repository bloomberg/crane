#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <regexp.h>
#include <string>
#include <utility>
#include <variant>

bool Matcher::char_eq(const int x, const int y) {
  bool b = x == y;
  if (b) {
    return true;
  } else {
    return false;
  }
}

bool Matcher::regexp_eq(const std::shared_ptr<Matcher::regexp> &r,
                        const std::shared_ptr<Matcher::regexp> &x) {
  return std::visit(
      Overloaded{
          [&](const typename Matcher::regexp::Any _args) -> T1 {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args) -> bool {
                      return true;
                    },
                    [&](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Char _args) -> T1 {
            int c = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Char _args) -> bool {
                      int c0 = _args._a0;
                      if (char_eq(c, c0)) {
                        return true;
                      } else {
                        return false;
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Eps _args) -> T1 {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Eps _args) -> bool {
                      return true;
                    },
                    [&](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Cat _args) -> T1 {
            std::shared_ptr<Matcher::regexp> r1 = _args._a0;
            std::shared_ptr<Matcher::regexp> r2 = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Cat _args) -> bool {
                      std::shared_ptr<Matcher::regexp> r3 = _args._a0;
                      std::shared_ptr<Matcher::regexp> r4 = _args._a1;
                      if (regexp_eq(r1, r3)) {
                        if (regexp_eq(r2, r4)) {
                          return true;
                        } else {
                          return false;
                        }
                      } else {
                        return false;
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Alt _args) -> T1 {
            std::shared_ptr<Matcher::regexp> r1 = _args._a0;
            std::shared_ptr<Matcher::regexp> r2 = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Alt _args) -> bool {
                      std::shared_ptr<Matcher::regexp> r3 = _args._a0;
                      std::shared_ptr<Matcher::regexp> r4 = _args._a1;
                      if (regexp_eq(r1, r3)) {
                        if (regexp_eq(r2, r4)) {
                          return true;
                        } else {
                          return false;
                        }
                      } else {
                        return false;
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Zero _args) -> T1 {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Zero _args) -> bool {
                      return true;
                    },
                    [&](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Star _args) -> T1 {
            std::shared_ptr<Matcher::regexp> r0 = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Star _args) -> bool {
                      std::shared_ptr<Matcher::regexp> r1 = _args._a0;
                      if (regexp_eq(r0, r1)) {
                        return true;
                      } else {
                        return false;
                      }
                    }},
                x->v());
          }},
      r->v());
}

std::shared_ptr<Matcher::regexp>
Matcher::OptCat(const std::shared_ptr<Matcher::regexp> &r1,
                const std::shared_ptr<Matcher::regexp> &r2) {
  return std::visit(
      Overloaded{
          [&](const typename Matcher::regexp::Any _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> { return r1; },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Zero_();
                    },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    }},
                r2->v());
          },
          [&](const typename Matcher::regexp::Char _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> { return r1; },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Zero_();
                    },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    }},
                r2->v());
          },
          [&](const typename Matcher::regexp::Eps _args)
              -> std::shared_ptr<Matcher::regexp> { return r2; },
          [&](const typename Matcher::regexp::Cat _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> { return r1; },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Zero_();
                    },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    }},
                r2->v());
          },
          [&](const typename Matcher::regexp::Alt _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> { return r1; },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Zero_();
                    },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    }},
                r2->v());
          },
          [&](const typename Matcher::regexp::Zero _args)
              -> std::shared_ptr<Matcher::regexp> {
            return regexp::ctor::Zero_();
          },
          [&](const typename Matcher::regexp::Star _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> { return r1; },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Zero_();
                    },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return regexp::ctor::Cat_(r1, r2);
                    }},
                r2->v());
          }},
      r1->v());
}

std::shared_ptr<Matcher::regexp>
Matcher::OptAlt(const std::shared_ptr<Matcher::regexp> &r1,
                const std::shared_ptr<Matcher::regexp> &r2) {
  return std::visit(
      Overloaded{
          [&](const typename Matcher::regexp::Any _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> { return r1; },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    }},
                r2->v());
          },
          [&](const typename Matcher::regexp::Char _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> { return r1; },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    }},
                r2->v());
          },
          [&](const typename Matcher::regexp::Eps _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> { return r1; },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    }},
                r2->v());
          },
          [&](const typename Matcher::regexp::Cat _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> { return r1; },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    }},
                r2->v());
          },
          [&](const typename Matcher::regexp::Alt _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> { return r1; },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    }},
                r2->v());
          },
          [&](const typename Matcher::regexp::Zero _args)
              -> std::shared_ptr<Matcher::regexp> { return r2; },
          [&](const typename Matcher::regexp::Star _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> { return r1; },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::ctor::Alt_(r1, r2);
                      }
                    }},
                r2->v());
          }},
      r1->v());
}

std::shared_ptr<Matcher::regexp>
Matcher::null(const std::shared_ptr<Matcher::regexp> &r) {
  return std::visit(
      Overloaded{[&](const typename Matcher::regexp::Any _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Zero_();
                 },
                 [&](const typename Matcher::regexp::Char _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Zero_();
                 },
                 [&](const typename Matcher::regexp::Eps _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Eps_();
                 },
                 [&](const typename Matcher::regexp::Cat _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   std::shared_ptr<Matcher::regexp> r1 = _args._a0;
                   std::shared_ptr<Matcher::regexp> r2 = _args._a1;
                   return OptCat(null(r1), null(r2));
                 },
                 [&](const typename Matcher::regexp::Alt _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   std::shared_ptr<Matcher::regexp> r1 = _args._a0;
                   std::shared_ptr<Matcher::regexp> r2 = _args._a1;
                   return OptAlt(null(r1), null(r2));
                 },
                 [&](const typename Matcher::regexp::Zero _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Zero_();
                 },
                 [&](const typename Matcher::regexp::Star _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Eps_();
                 }},
      r->v());
}

bool Matcher::accepts_null(const std::shared_ptr<Matcher::regexp> &r) {
  return regexp_eq(null(r), regexp::ctor::Eps_());
}

std::shared_ptr<Matcher::regexp>
Matcher::deriv(const std::shared_ptr<Matcher::regexp> &r, const int c) {
  return std::visit(
      Overloaded{[&](const typename Matcher::regexp::Any _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Eps_();
                 },
                 [&](const typename Matcher::regexp::Char _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   int c_ = _args._a0;
                   if (char_eq(c, c_)) {
                     return regexp::ctor::Eps_();
                   } else {
                     return regexp::ctor::Zero_();
                   }
                 },
                 [&](const typename Matcher::regexp::Eps _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Zero_();
                 },
                 [&](const typename Matcher::regexp::Cat _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   std::shared_ptr<Matcher::regexp> r1 = _args._a0;
                   std::shared_ptr<Matcher::regexp> r2 = _args._a1;
                   return OptAlt(OptCat(deriv(r1, c), r2),
                                 OptCat(null(r1), deriv(r2, c)));
                 },
                 [&](const typename Matcher::regexp::Alt _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   std::shared_ptr<Matcher::regexp> r1 = _args._a0;
                   std::shared_ptr<Matcher::regexp> r2 = _args._a1;
                   return OptAlt(deriv(r1, c), deriv(r2, c));
                 },
                 [&](const typename Matcher::regexp::Zero _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Zero_();
                 },
                 [&](const typename Matcher::regexp::Star _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   std::shared_ptr<Matcher::regexp> r0 = _args._a0;
                   return OptCat(deriv(r0, c), regexp::ctor::Star_(r0));
                 }},
      r->v());
}

std::shared_ptr<Matcher::regexp>
Matcher::derivs(const std::shared_ptr<Matcher::regexp> &r,
                const std::shared_ptr<List::list<int>> &cs) {
  return std::visit(
      Overloaded{[&](const typename List::list<int>::nil _args)
                     -> std::shared_ptr<Matcher::regexp> { return r; },
                 [&](const typename List::list<int>::cons _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   int c = _args._a0;
                   std::shared_ptr<List::list<int>> cs_ = _args._a1;
                   return derivs(deriv(r, c), cs_);
                 }},
      cs->v());
}

bool Matcher::deriv_parse(const std::shared_ptr<Matcher::regexp> &r,
                          const std::shared_ptr<List::list<int>> &cs) {
  if (accepts_null(derivs(r, cs))) {
    return true;
  } else {
    return false;
  }
}

bool Matcher::NullEpsOrZero(const std::shared_ptr<Matcher::regexp> &r) {
  return std::visit(
      Overloaded{
          [&](const typename Matcher::regexp::Any _args) -> T1 {
            return false;
          },
          [&](const typename Matcher::regexp::Char _args) -> T1 {
            return false;
          },
          [&](const typename Matcher::regexp::Eps _args) -> T1 { return true; },
          [&](const typename Matcher::regexp::Cat _args) -> T1 {
            std::shared_ptr<Matcher::regexp> r1 = _args._a0;
            std::shared_ptr<Matcher::regexp> r2 = _args._a1;
            if (NullEpsOrZero(r1)) {
              if (NullEpsOrZero(r2)) {
                return true;
              } else {
                return false;
              }
            } else {
              if (NullEpsOrZero(r2)) {
                return false;
              } else {
                return false;
              }
            }
          },
          [&](const typename Matcher::regexp::Alt _args) -> T1 {
            std::shared_ptr<Matcher::regexp> r1 = _args._a0;
            std::shared_ptr<Matcher::regexp> r2 = _args._a1;
            if (NullEpsOrZero(r1)) {
              if (NullEpsOrZero(r2)) {
                return true;
              } else {
                return true;
              }
            } else {
              if (NullEpsOrZero(r2)) {
                return true;
              } else {
                return false;
              }
            }
          },
          [&](const typename Matcher::regexp::Zero _args) -> T1 {
            return false;
          },
          [&](const typename Matcher::regexp::Star _args) -> T1 {
            return true;
          }},
      r->v());
}

bool Matcher::parse(const std::shared_ptr<Matcher::regexp> &r,
                    const std::shared_ptr<List::list<int>> &cs) {
  bool b = deriv_parse(r, cs);
  if (b) {
    return true;
  } else {
    return false;
  }
}

bool Matcher::parse_bool(const std::shared_ptr<Matcher::regexp> &r,
                         const std::shared_ptr<List::list<int>> &cs) {
  if (parse(r, cs)) {
    return true;
  } else {
    return false;
  }
}
