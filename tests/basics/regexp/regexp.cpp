#include <regexp.h>

#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
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
                    [](const typename Matcher::regexp::Any _args0) -> bool {
                      return true;
                    },
                    [](const typename Matcher::regexp::Char _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Cat _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Alt _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Star _args0) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Char _args) -> auto {
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args0) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Char _args0) -> bool {
                      if (char_eq(_args.d_c, _args0.d_c)) {
                        return true;
                      } else {
                        return false;
                      }
                    },
                    [](const typename Matcher::regexp::Eps _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Cat _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Alt _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Star _args0) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Eps _args) -> auto {
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Char _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args0) -> bool {
                      return true;
                    },
                    [](const typename Matcher::regexp::Cat _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Alt _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Star _args0) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Cat _args) -> auto {
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Char _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args0) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Cat _args0) -> bool {
                      if (regexp_eq(_args.d_r1, _args0.d_r1)) {
                        if (regexp_eq(_args.d_r2, _args0.d_r2)) {
                          return true;
                        } else {
                          return false;
                        }
                      } else {
                        return false;
                      }
                    },
                    [](const typename Matcher::regexp::Alt _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Star _args0) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Alt _args) -> auto {
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Char _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Cat _args0) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Alt _args0) -> bool {
                      if (regexp_eq(_args.d_r1, _args0.d_r1)) {
                        if (regexp_eq(_args.d_r2, _args0.d_r2)) {
                          return true;
                        } else {
                          return false;
                        }
                      } else {
                        return false;
                      }
                    },
                    [](const typename Matcher::regexp::Zero _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Star _args0) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Zero _args) -> auto {
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Char _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Cat _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Alt _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args0) -> bool {
                      return true;
                    },
                    [](const typename Matcher::regexp::Star _args0) -> bool {
                      return false;
                    }},
                x->v());
          },
          [&](const typename Matcher::regexp::Star _args) -> auto {
            return std::visit(
                Overloaded{
                    [](const typename Matcher::regexp::Any _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Char _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Eps _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Cat _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Alt _args0) -> bool {
                      return false;
                    },
                    [](const typename Matcher::regexp::Zero _args0) -> bool {
                      return false;
                    },
                    [&](const typename Matcher::regexp::Star _args0) -> bool {
                      if (regexp_eq(_args.d_r, _args0.d_r)) {
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
Matcher::OptCat(std::shared_ptr<Matcher::regexp> r2,
                std::shared_ptr<Matcher::regexp> r3) {
  return [&](void) {
    if (r2.use_count() == 1 && r2->v().index() == 5) {
      auto &_rf = std::get<5>(r2->v_mut());
      return r2;
    } else {
      return std::visit(
          Overloaded{
              [&](const typename Matcher::regexp::Any _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return [&](void) {
                  if (r3.use_count() == 1 && r3->v().index() == 3) {
                    auto &_rf = std::get<3>(r3->v_mut());
                    _rf.d_r1 = r2;
                    _rf.d_r2 = r3;
                    return r3;
                  } else {
                    return std::visit(
                        Overloaded{
                            [&](const typename Matcher::regexp::Any _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Char _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Eps _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return std::move(r2);
                            },
                            [&](const typename Matcher::regexp::Cat _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Alt _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [](const typename Matcher::regexp::Zero _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::zero();
                            },
                            [&](const typename Matcher::regexp::Star _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            }},
                        r3->v());
                  }
                }();
              },
              [&](const typename Matcher::regexp::Char _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return [&](void) {
                  if (r3.use_count() == 1 && r3->v().index() == 3) {
                    auto &_rf = std::get<3>(r3->v_mut());
                    _rf.d_r1 = r2;
                    _rf.d_r2 = r3;
                    return r3;
                  } else {
                    return std::visit(
                        Overloaded{
                            [&](const typename Matcher::regexp::Any _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Char _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Eps _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return std::move(r2);
                            },
                            [&](const typename Matcher::regexp::Cat _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Alt _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [](const typename Matcher::regexp::Zero _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::zero();
                            },
                            [&](const typename Matcher::regexp::Star _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            }},
                        r3->v());
                  }
                }();
              },
              [&](const typename Matcher::regexp::Eps _args)
                  -> std::shared_ptr<Matcher::regexp> { return std::move(r3); },
              [&](const typename Matcher::regexp::Cat _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return [&](void) {
                  if (r3.use_count() == 1 && r3->v().index() == 3) {
                    auto &_rf = std::get<3>(r3->v_mut());
                    _rf.d_r1 = r2;
                    _rf.d_r2 = r3;
                    return r3;
                  } else {
                    return std::visit(
                        Overloaded{
                            [&](const typename Matcher::regexp::Any _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Char _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Eps _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return std::move(r2);
                            },
                            [&](const typename Matcher::regexp::Cat _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Alt _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [](const typename Matcher::regexp::Zero _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::zero();
                            },
                            [&](const typename Matcher::regexp::Star _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            }},
                        r3->v());
                  }
                }();
              },
              [&](const typename Matcher::regexp::Alt _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return [&](void) {
                  if (r3.use_count() == 1 && r3->v().index() == 3) {
                    auto &_rf = std::get<3>(r3->v_mut());
                    _rf.d_r1 = r2;
                    _rf.d_r2 = r3;
                    return r3;
                  } else {
                    return std::visit(
                        Overloaded{
                            [&](const typename Matcher::regexp::Any _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Char _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Eps _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return std::move(r2);
                            },
                            [&](const typename Matcher::regexp::Cat _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Alt _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [](const typename Matcher::regexp::Zero _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::zero();
                            },
                            [&](const typename Matcher::regexp::Star _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            }},
                        r3->v());
                  }
                }();
              },
              [](const typename Matcher::regexp::Zero _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return regexp::zero();
              },
              [&](const typename Matcher::regexp::Star _args)
                  -> std::shared_ptr<Matcher::regexp> {
                return [&](void) {
                  if (r3.use_count() == 1 && r3->v().index() == 3) {
                    auto &_rf = std::get<3>(r3->v_mut());
                    _rf.d_r1 = r2;
                    _rf.d_r2 = r3;
                    return r3;
                  } else {
                    return std::visit(
                        Overloaded{
                            [&](const typename Matcher::regexp::Any _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Char _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Eps _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return std::move(r2);
                            },
                            [&](const typename Matcher::regexp::Cat _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [&](const typename Matcher::regexp::Alt _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            },
                            [](const typename Matcher::regexp::Zero _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::zero();
                            },
                            [&](const typename Matcher::regexp::Star _args0)
                                -> std::shared_ptr<Matcher::regexp> {
                              return regexp::cat(std::move(r2), std::move(r3));
                            }},
                        r3->v());
                  }
                }();
              }},
          r2->v());
    }
  }();
}

/// Optimized version of Alt.
std::shared_ptr<Matcher::regexp>
Matcher::OptAlt(std::shared_ptr<Matcher::regexp> r2,
                std::shared_ptr<Matcher::regexp> r3) {
  return std::visit(
      Overloaded{
          [&](const typename Matcher::regexp::Any _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{[&](const typename Matcher::regexp::Any _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Char _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Eps _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Cat _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Alt _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Zero _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             return std::move(r2);
                           },
                           [&](const typename Matcher::regexp::Star _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           }},
                r3->v());
          },
          [&](const typename Matcher::regexp::Char _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{[&](const typename Matcher::regexp::Any _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Char _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Eps _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Cat _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Alt _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Zero _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             return std::move(r2);
                           },
                           [&](const typename Matcher::regexp::Star _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           }},
                r3->v());
          },
          [&](const typename Matcher::regexp::Eps _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{[&](const typename Matcher::regexp::Any _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Char _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Eps _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Cat _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Alt _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Zero _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             return std::move(r2);
                           },
                           [&](const typename Matcher::regexp::Star _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           }},
                r3->v());
          },
          [&](const typename Matcher::regexp::Cat _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{[&](const typename Matcher::regexp::Any _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Char _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Eps _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Cat _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Alt _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Zero _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             return std::move(r2);
                           },
                           [&](const typename Matcher::regexp::Star _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           }},
                r3->v());
          },
          [&](const typename Matcher::regexp::Alt _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{[&](const typename Matcher::regexp::Any _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Char _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Eps _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Cat _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Alt _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Zero _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             return std::move(r2);
                           },
                           [&](const typename Matcher::regexp::Star _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           }},
                r3->v());
          },
          [&](const typename Matcher::regexp::Zero _args)
              -> std::shared_ptr<Matcher::regexp> { return std::move(r3); },
          [&](const typename Matcher::regexp::Star _args)
              -> std::shared_ptr<Matcher::regexp> {
            return std::visit(
                Overloaded{[&](const typename Matcher::regexp::Any _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Char _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Eps _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Cat _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Alt _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           },
                           [&](const typename Matcher::regexp::Zero _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             return std::move(r2);
                           },
                           [&](const typename Matcher::regexp::Star _args0)
                               -> std::shared_ptr<Matcher::regexp> {
                             if (regexp_eq(r2, r3)) {
                               return std::move(r2);
                             } else {
                               return regexp::alt(std::move(r2), std::move(r3));
                             }
                           }},
                r3->v());
          }},
      r2->v());
}

/// If r accepts the empty string, return Eps, else return Zero.
std::shared_ptr<Matcher::regexp>
Matcher::null(const std::shared_ptr<Matcher::regexp> &r) {
  return std::visit(
      Overloaded{
          [](const typename Matcher::regexp::Any _args)
              -> std::shared_ptr<Matcher::regexp> { return regexp::zero(); },
          [](const typename Matcher::regexp::Char _args)
              -> std::shared_ptr<Matcher::regexp> { return regexp::zero(); },
          [](const typename Matcher::regexp::Eps _args)
              -> std::shared_ptr<Matcher::regexp> { return regexp::eps(); },
          [](const typename Matcher::regexp::Cat _args)
              -> std::shared_ptr<Matcher::regexp> {
            return OptCat(null(_args.d_r1), null(_args.d_r2));
          },
          [](const typename Matcher::regexp::Alt _args)
              -> std::shared_ptr<Matcher::regexp> {
            return OptAlt(null(_args.d_r1), null(_args.d_r2));
          },
          [](const typename Matcher::regexp::Zero _args)
              -> std::shared_ptr<Matcher::regexp> { return regexp::zero(); },
          [](const typename Matcher::regexp::Star _args)
              -> std::shared_ptr<Matcher::regexp> { return regexp::eps(); }},
      r->v());
}

__attribute__((pure)) bool
Matcher::accepts_null(const std::shared_ptr<Matcher::regexp> &r) {
  return regexp_eq(null(r), regexp::eps());
}

/// This is the heart of the algorithm.  It returns a regexp denoting
/// { cs | (c::cs) in r }.
std::shared_ptr<Matcher::regexp>
Matcher::deriv(const std::shared_ptr<Matcher::regexp> &r, const int64_t c) {
  return std::visit(
      Overloaded{
          [](const typename Matcher::regexp::Any _args)
              -> std::shared_ptr<Matcher::regexp> { return regexp::eps(); },
          [&](const typename Matcher::regexp::Char _args)
              -> std::shared_ptr<Matcher::regexp> {
            if (char_eq(c, _args.d_c)) {
              return regexp::eps();
            } else {
              return regexp::zero();
            }
          },
          [](const typename Matcher::regexp::Eps _args)
              -> std::shared_ptr<Matcher::regexp> { return regexp::zero(); },
          [&](const typename Matcher::regexp::Cat _args)
              -> std::shared_ptr<Matcher::regexp> {
            return OptAlt(OptCat(deriv(_args.d_r1, c), _args.d_r2),
                          OptCat(null(_args.d_r1), deriv(_args.d_r2, c)));
          },
          [&](const typename Matcher::regexp::Alt _args)
              -> std::shared_ptr<Matcher::regexp> {
            return OptAlt(deriv(_args.d_r1, c), deriv(_args.d_r2, c));
          },
          [](const typename Matcher::regexp::Zero _args)
              -> std::shared_ptr<Matcher::regexp> { return regexp::zero(); },
          [&](const typename Matcher::regexp::Star _args)
              -> std::shared_ptr<Matcher::regexp> {
            return OptCat(deriv(_args.d_r, c), regexp::star(_args.d_r));
          }},
      r->v());
}

/// This calculates the derivative of a regular expression with respect to a
/// string.
std::shared_ptr<Matcher::regexp>
Matcher::derivs(std::shared_ptr<Matcher::regexp> r,
                const std::shared_ptr<List<int64_t>> &cs) {
  return std::visit(Overloaded{[&](const typename List<int64_t>::Nil _args)
                                   -> std::shared_ptr<Matcher::regexp> {
                                 return std::move(r);
                               },
                               [&](const typename List<int64_t>::Cons _args)
                                   -> std::shared_ptr<Matcher::regexp> {
                                 return derivs(deriv(std::move(r), _args.d_a0),
                                               _args.d_a1);
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
                   if (NullEpsOrZero(_args.d_r1)) {
                     if (NullEpsOrZero(_args.d_r2)) {
                       return true;
                     } else {
                       return false;
                     }
                   } else {
                     if (NullEpsOrZero(_args.d_r2)) {
                       return false;
                     } else {
                       return false;
                     }
                   }
                 },
                 [](const typename Matcher::regexp::Alt _args) -> auto {
                   if (NullEpsOrZero(_args.d_r1)) {
                     if (NullEpsOrZero(_args.d_r2)) {
                       return true;
                     } else {
                       return true;
                     }
                   } else {
                     if (NullEpsOrZero(_args.d_r2)) {
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
