#include <regexp.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) bool Matcher::char_eq(const int64_t x, const int64_t y) {
  bool b = x == y;
  if (std::move(b)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool
Matcher::regexp_eq(const std::shared_ptr<Matcher::regexp> &r,
                   const std::shared_ptr<Matcher::regexp> &x) {
  return std::visit(
      Overloaded{
          [&](const typename Matcher::regexp::Any _args) -> auto {
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args) -> bool {
                      return true;
                    },
                    [](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Char _args) -> auto {
            int64_t c = _args.d_a0;
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Char _args) -> bool {
                      int64_t c0 = _args.d_a0;
                      if (char_eq(c, c0)) {
                        return true;
                      } else {
                        return false;
                      }
                    },
                    [](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Eps _args) -> auto {
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args) -> bool {
                      return true;
                    },
                    [](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Cat _args) -> auto {
            std::shared_ptr<Matcher::regexp> r1 = _args.d_a0;
            std::shared_ptr<Matcher::regexp> r2 = _args.d_a1;
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Cat _args) -> bool {
                      std::shared_ptr<Matcher::regexp> r3 = _args.d_a0;
                      std::shared_ptr<Matcher::regexp> r4 = _args.d_a1;
                      if (regexp_eq(std::move(r1), std::move(r3))) {
                        if (regexp_eq(std::move(r2), std::move(r4))) {
                          return true;
                        } else {
                          return false;
                        }
                      } else {
                        return false;
                      }
                    },
                    [](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Alt _args) -> auto {
            std::shared_ptr<Matcher::regexp> r1 = _args.d_a0;
            std::shared_ptr<Matcher::regexp> r2 = _args.d_a1;
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Alt _args) -> bool {
                      std::shared_ptr<Matcher::regexp> r3 = _args.d_a0;
                      std::shared_ptr<Matcher::regexp> r4 = _args.d_a1;
                      if (regexp_eq(std::move(r1), std::move(r3))) {
                        if (regexp_eq(std::move(r2), std::move(r4))) {
                          return true;
                        } else {
                          return false;
                        }
                      } else {
                        return false;
                      }
                    },
                    [](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Zero _args) -> auto {
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args) -> bool {
                      return true;
                    },
                    [](const typename Matcher::regexp::Star _args) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Star _args) -> auto {
            std::shared_ptr<Matcher::regexp> r0 = _args.d_a0;
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Char _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Cat _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Alt _args) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Star _args) -> bool {
                      std::shared_ptr<Matcher::regexp> r1 = _args.d_a0;
                      if (regexp_eq(std::move(r0), std::move(r1))) {
                        return true;
                      } else {
                        return false;
                      }
                    }},
                x->v());
          }},
      r->v());
}

/// An optimized constructor for Cat.
std::shared_ptr<Matcher::regexp>
Matcher::OptCat(std::shared_ptr<Matcher::regexp> r1,
                std::shared_ptr<Matcher::regexp> r2) {
  return [&](void) {
    if (r1.use_count() == 1 && r1->v().index() == 5) {
      auto &_rf = std::get<5>(r1->v_mut());
      return r1;
    } else {
      return std::visit(
          Overloaded{
              [&](const typename Matcher::regexp::Any _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return [&](void) {
                  if (r2.use_count() == 1 && r2->v().index() == 3) {
                    auto &_rf = std::get<3>(r2->v_mut());
                    _rf.d_a0 = r1;
                    _rf.d_a1 = r2;
                    return r2;
                  } else {
                    return std::visit(
                        Overloaded{
                            [&](const typename Matcher::regexp::Any _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Char _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Eps _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return std::move(r1);
                            },
                            [&](const typename Matcher::regexp::Cat _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Alt _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [](const typename Matcher::regexp::Zero _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Zero_();
                            },
                            [&](const typename Matcher::regexp::Star _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            }},
                        r2->v());
                  }
                }();
              },
              [&](const typename Matcher::regexp::Char _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return [&](void) {
                  if (r2.use_count() == 1 && r2->v().index() == 3) {
                    auto &_rf = std::get<3>(r2->v_mut());
                    _rf.d_a0 = r1;
                    _rf.d_a1 = r2;
                    return r2;
                  } else {
                    return std::visit(
                        Overloaded{
                            [&](const typename Matcher::regexp::Any _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Char _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Eps _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return std::move(r1);
                            },
                            [&](const typename Matcher::regexp::Cat _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Alt _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [](const typename Matcher::regexp::Zero _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Zero_();
                            },
                            [&](const typename Matcher::regexp::Star _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            }},
                        r2->v());
                  }
                }();
              },
              [&](const typename Matcher::regexp::Eps _args)
                  -> std::shared_ptr<Matcher::regexp> { return std::move(r2); },
              [&](const typename Matcher::regexp::Cat _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return [&](void) {
                  if (r2.use_count() == 1 && r2->v().index() == 3) {
                    auto &_rf = std::get<3>(r2->v_mut());
                    _rf.d_a0 = r1;
                    _rf.d_a1 = r2;
                    return r2;
                  } else {
                    return std::visit(
                        Overloaded{
                            [&](const typename Matcher::regexp::Any _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Char _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Eps _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return std::move(r1);
                            },
                            [&](const typename Matcher::regexp::Cat _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Alt _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [](const typename Matcher::regexp::Zero _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Zero_();
                            },
                            [&](const typename Matcher::regexp::Star _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            }},
                        r2->v());
                  }
                }();
              },
              [&](const typename Matcher::regexp::Alt _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return [&](void) {
                  if (r2.use_count() == 1 && r2->v().index() == 3) {
                    auto &_rf = std::get<3>(r2->v_mut());
                    _rf.d_a0 = r1;
                    _rf.d_a1 = r2;
                    return r2;
                  } else {
                    return std::visit(
                        Overloaded{
                            [&](const typename Matcher::regexp::Any _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Char _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Eps _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return std::move(r1);
                            },
                            [&](const typename Matcher::regexp::Cat _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Alt _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [](const typename Matcher::regexp::Zero _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Zero_();
                            },
                            [&](const typename Matcher::regexp::Star _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            }},
                        r2->v());
                  }
                }();
              },
              [](const typename Matcher::regexp::Zero _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return regexp::ctor::Zero_();
              },
              [&](const typename Matcher::regexp::Star _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return [&](void) {
                  if (r2.use_count() == 1 && r2->v().index() == 3) {
                    auto &_rf = std::get<3>(r2->v_mut());
                    _rf.d_a0 = r1;
                    _rf.d_a1 = r2;
                    return r2;
                  } else {
                    return std::visit(
                        Overloaded{
                            [&](const typename Matcher::regexp::Any _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Char _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Eps _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return std::move(r1);
                            },
                            [&](const typename Matcher::regexp::Cat _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [&](const typename Matcher::regexp::Alt _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            },
                            [](const typename Matcher::regexp::Zero _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Zero_();
                            },
                            [&](const typename Matcher::regexp::Star _args)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::ctor::Cat_(std::move(r1),
                                                        std::move(r2));
                            }},
                        r2->v());
                  }
                }();
              }},
          r1->v());
    }
  }();
}

/// Optimized version of Alt.
std::shared_ptr<Matcher::regexp>
Matcher::OptAlt(std::shared_ptr<Matcher::regexp> r1,
                std::shared_ptr<Matcher::regexp> r2) {
  return std::visit(
      Overloaded{
          [&](const typename Matcher::regexp::Any _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return std::move(r1);
                    },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
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
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return std::move(r1);
                    },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
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
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return std::move(r1);
                    },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
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
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return std::move(r1);
                    },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
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
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return std::move(r1);
                    },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    }},
                r2->v());
          },
          [&](const typename Matcher::regexp::Zero _args)
              -> std::shared_ptr<Matcher::regexp> { return std::move(r2); },
          [&](const typename Matcher::regexp::Star _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{
                    [&](const typename Matcher::regexp::Any _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Char _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Eps _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Cat _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Alt _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    },
                    [&](const typename Matcher::regexp::Zero _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      return std::move(r1);
                    },
                    [&](const typename Matcher::regexp::Star _args)
                        -> std::shared_ptr<Matcher::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return std::move(r1);
                      } else {
                        return regexp::ctor::Alt_(std::move(r1), std::move(r2));
                      }
                    }},
                r2->v());
          }},
      r1->v());
}

/// If r accepts the empty string, return Eps, else return Zero.
std::shared_ptr<Matcher::regexp>
Matcher::null(const std::shared_ptr<Matcher::regexp> &r) {
  return std::visit(
      Overloaded{[](const typename Matcher::regexp::Any _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Zero_();
                 },
                 [](const typename Matcher::regexp::Char _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Zero_();
                 },
                 [](const typename Matcher::regexp::Eps _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Eps_();
                 },
                 [](const typename Matcher::regexp::Cat _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   std::shared_ptr<Matcher::regexp> r1 = _args.d_a0;
                   std::shared_ptr<Matcher::regexp> r2 = _args.d_a1;
                   return OptCat(null(std::move(r1)), null(std::move(r2)));
                 },
                 [](const typename Matcher::regexp::Alt _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   std::shared_ptr<Matcher::regexp> r1 = _args.d_a0;
                   std::shared_ptr<Matcher::regexp> r2 = _args.d_a1;
                   return OptAlt(null(std::move(r1)), null(std::move(r2)));
                 },
                 [](const typename Matcher::regexp::Zero _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Zero_();
                 },
                 [](const typename Matcher::regexp::Star _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Eps_();
                 }},
      r->v());
}

__attribute__((pure)) bool
Matcher::accepts_null(const std::shared_ptr<Matcher::regexp> &r) {
  return regexp_eq(null(r), regexp::ctor::Eps_());
}

/// This is the heart of the algorithm.  It returns a regexp denoting
/// { cs | (c::cs) in r }.
std::shared_ptr<Matcher::regexp>
Matcher::deriv(const std::shared_ptr<Matcher::regexp> &r, const int64_t c) {
  return std::visit(
      Overloaded{[](const typename Matcher::regexp::Any _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Eps_();
                 },
                 [&](const typename Matcher::regexp::Char _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   int64_t c_ = _args.d_a0;
                   if (char_eq(c, c_)) {
                     return regexp::ctor::Eps_();
                   } else {
                     return regexp::ctor::Zero_();
                   }
                 },
                 [](const typename Matcher::regexp::Eps _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Zero_();
                 },
                 [&](const typename Matcher::regexp::Cat _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   std::shared_ptr<Matcher::regexp> r1 = _args.d_a0;
                   std::shared_ptr<Matcher::regexp> r2 = _args.d_a1;
                   return OptAlt(OptCat(deriv(r1, c), r2),
                                 OptCat(null(r1), deriv(r2, c)));
                 },
                 [&](const typename Matcher::regexp::Alt _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   std::shared_ptr<Matcher::regexp> r1 = _args.d_a0;
                   std::shared_ptr<Matcher::regexp> r2 = _args.d_a1;
                   return OptAlt(deriv(std::move(r1), c),
                                 deriv(std::move(r2), c));
                 },
                 [](const typename Matcher::regexp::Zero _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   return regexp::ctor::Zero_();
                 },
                 [&](const typename Matcher::regexp::Star _args)
                     -> std::shared_ptr<Matcher::regexp> {
                   std::shared_ptr<Matcher::regexp> r0 = _args.d_a0;
                   return OptCat(deriv(r0, c), regexp::ctor::Star_(r0));
                 }},
      r->v());
}

/// This calculates the derivative of a regular expression with respect to a
/// string.
std::shared_ptr<Matcher::regexp>
Matcher::derivs(std::shared_ptr<Matcher::regexp> r,
                const std::shared_ptr<List<int64_t>> &cs) {
  return std::visit(
      Overloaded{
          [&](const typename List<int64_t>::Nil _args)
              -> std::shared_ptr<Matcher::regexp> { return std::move(r); },
          [&](const typename List<int64_t>::Cons _args)
              -> std::shared_ptr<Matcher::regexp> {
            int64_t c = _args.d_a0;
            std::shared_ptr<List<int64_t>> cs_ = _args.d_a1;
            return derivs(deriv(std::move(r), c), std::move(cs_));
          }},
      cs->v());
}

/// To see if cs matches r, calculate the derivative of r with respect
/// to s, and see if the resulting regexp accepts the empty string.
__attribute__((pure)) bool
Matcher::deriv_parse(const std::shared_ptr<Matcher::regexp> &r,
                     const std::shared_ptr<List<int64_t>> &cs) {
  if (accepts_null(derivs(r, cs))) {
    return true;
  } else {
    return false;
  }
}

/// null r returns Eps or Zero
__attribute__((pure)) bool
Matcher::NullEpsOrZero(const std::shared_ptr<Matcher::regexp> &r) {
  return std::visit(
      Overloaded{[](const typename Matcher::regexp::Any _args) -> auto {
                   return false;
                 },
                 [](const typename Matcher::regexp::Char _args) -> auto {
                   return false;
                 },
                 [](const typename Matcher::regexp::Eps _args) -> auto {
                   return true;
                 },
                 [](const typename Matcher::regexp::Cat _args) -> auto {
                   std::shared_ptr<Matcher::regexp> r1 = _args.d_a0;
                   std::shared_ptr<Matcher::regexp> r2 = _args.d_a1;
                   if (NullEpsOrZero(std::move(r1))) {
                     if (NullEpsOrZero(std::move(r2))) {
                       return true;
                     } else {
                       return false;
                     }
                   } else {
                     if (NullEpsOrZero(std::move(r2))) {
                       return false;
                     } else {
                       return false;
                     }
                   }
                 },
                 [](const typename Matcher::regexp::Alt _args) -> auto {
                   std::shared_ptr<Matcher::regexp> r1 = _args.d_a0;
                   std::shared_ptr<Matcher::regexp> r2 = _args.d_a1;
                   if (NullEpsOrZero(std::move(r1))) {
                     if (NullEpsOrZero(std::move(r2))) {
                       return true;
                     } else {
                       return true;
                     }
                   } else {
                     if (NullEpsOrZero(std::move(r2))) {
                       return true;
                     } else {
                       return false;
                     }
                   }
                 },
                 [](const typename Matcher::regexp::Zero _args) -> auto {
                   return false;
                 },
                 [](const typename Matcher::regexp::Star _args) -> auto {
                   return true;
                 }},
      r->v());
}

/// From this, we can build a decidable regexp matcher by running
/// the derivative-based parser.
__attribute__((pure)) bool
Matcher::parse(const std::shared_ptr<Matcher::regexp> &r,
               const std::shared_ptr<List<int64_t>> &cs) {
  bool b = deriv_parse(r, cs);
  if (std::move(b)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool
Matcher::parse_bool(const std::shared_ptr<Matcher::regexp> &r,
                    const std::shared_ptr<List<int64_t>> &cs) {
  if (parse(r, cs)) {
    return true;
  } else {
    return false;
  }
}
