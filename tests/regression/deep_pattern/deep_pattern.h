#ifndef INCLUDED_DEEP_PATTERN
#define INCLUDED_DEEP_PATTERN

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct DeepPattern {
  struct tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      std::shared_ptr<tree> d_a0;
      std::shared_ptr<tree> d_a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> leaf(unsigned int a0) {
      return std::make_shared<tree>(Leaf{std::move(a0)});
    }

    static std::shared_ptr<tree> node(const std::shared_ptr<tree> &a0,
                                      const std::shared_ptr<tree> &a1) {
      return std::make_shared<tree>(Node{a0, a1});
    }

    static std::shared_ptr<tree> node(std::shared_ptr<tree> &&a0,
                                      std::shared_ptr<tree> &&a1) {
      return std::make_shared<tree>(Node{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int nested_let_match() const {
      return std::visit(
          Overloaded{
              [](const typename tree::Leaf &_args) -> unsigned int {
                return _args.d_a0;
              },
              [](const typename tree::Node &_args) -> unsigned int {
                unsigned int a = std::visit(
                    Overloaded{[](const typename tree::Leaf &_args0)
                                   -> unsigned int { return _args0.d_a0; },
                               [](const typename tree::Node &) -> unsigned int {
                                 return 0u;
                               }},
                    _args.d_a0->v());
                unsigned int b = std::visit(
                    Overloaded{[](const typename tree::Leaf &_args1)
                                   -> unsigned int { return _args1.d_a0; },
                               [](const typename tree::Node &) -> unsigned int {
                                 return 0u;
                               }},
                    _args.d_a1->v());
                unsigned int c = (a + b);
                unsigned int d = (c * 2u);
                return (d + 1u);
              }},
          this->v());
    }

    __attribute__((pure)) unsigned int
    conditional_match(const unsigned int target) const {
      return std::visit(
          Overloaded{[&](const typename tree::Leaf &_args) -> unsigned int {
                       if (_args.d_a0 == target) {
                         return 100u;
                       } else {
                         return _args.d_a0;
                       }
                     },
                     [&](const typename tree::Node &_args) -> unsigned int {
                       if (this->has_value(target)) {
                         return 200u;
                       } else {
                         return std::visit(
                             Overloaded{
                                 [](const typename tree::Leaf &_args0)
                                     -> unsigned int { return _args0.d_a0; },
                                 [](const typename tree::Node &)
                                     -> unsigned int { return 0u; }},
                             _args.d_a0->v());
                       }
                     }},
          this->v());
    }

    __attribute__((pure)) bool has_value(const unsigned int target) const {
      return std::visit(
          Overloaded{[&](const typename tree::Leaf &_args) -> bool {
                       return _args.d_a0 == target;
                     },
                     [&](const typename tree::Node &_args) -> bool {
                       return (_args.d_a0->has_value(target) ||
                               _args.d_a1->has_value(target));
                     }},
          this->v());
    }

    __attribute__((pure)) unsigned int wildcard_with_bindings() const {
      return std::visit(
          Overloaded{
              [](const typename tree::Leaf &_args) -> unsigned int {
                return _args.d_a0;
              },
              [](const typename tree::Node &_args) -> unsigned int {
                unsigned int x = std::visit(
                    Overloaded{[](const typename tree::Leaf &_args0)
                                   -> unsigned int { return _args0.d_a0; },
                               [](const typename tree::Node &) -> unsigned int {
                                 return 0u;
                               }},
                    _args.d_a0->v());
                unsigned int y = std::visit(
                    Overloaded{[](const typename tree::Leaf &_args1)
                                   -> unsigned int { return _args1.d_a0; },
                               [](const typename tree::Node &) -> unsigned int {
                                 return 0u;
                               }},
                    _args.d_a1->v());
                return (x + y);
              }},
          this->v());
    }

    __attribute__((pure)) unsigned int
    multi_constructor(const std::shared_ptr<tree> &t2) const {
      return std::visit(
          Overloaded{
              [&](const typename tree::Leaf &_args) -> unsigned int {
                return std::visit(
                    Overloaded{
                        [&](const typename tree::Leaf &_args0) -> unsigned int {
                          return (_args.d_a0 + _args0.d_a0);
                        },
                        [&](const typename tree::Node &_args0) -> unsigned int {
                          return std::visit(
                              Overloaded{[&](const typename tree::Leaf &_args1)
                                             -> unsigned int {
                                           return (_args.d_a0 + _args1.d_a0);
                                         },
                                         [](const typename tree::Node &)
                                             -> unsigned int { return 0u; }},
                              _args0.d_a0->v());
                        }},
                    t2->v());
              },
              [&](const typename tree::Node &_args) -> unsigned int {
                return std::visit(
                    Overloaded{
                        [&](const typename tree::Leaf &_args0) -> unsigned int {
                          return std::visit(
                              Overloaded{
                                  [&](const typename tree::Leaf &_args1)
                                      -> unsigned int {
                                    return std::visit(
                                        Overloaded{
                                            [&](const typename tree::Leaf
                                                    &_args2) -> unsigned int {
                                              return (_args0.d_a0 +
                                                      _args2.d_a0);
                                            },
                                            [&](const typename tree::Node
                                                    &_args2) -> unsigned int {
                                              return std::visit(
                                                  Overloaded{
                                                      [&](const typename tree::
                                                              Leaf &_args3)
                                                          -> unsigned int {
                                                        return std::visit(
                                                            Overloaded{
                                                                [&](const typename tree::
                                                                        Leaf &
                                                                            _args4)
                                                                    -> unsigned int {
                                                                  return (
                                                                      ((_args0
                                                                            .d_a0 +
                                                                        _args1
                                                                            .d_a0) +
                                                                       _args3
                                                                           .d_a0) +
                                                                      _args4
                                                                          .d_a0);
                                                                },
                                                                [](const typename tree::
                                                                       Node &)
                                                                    -> unsigned int {
                                                                  return 0u;
                                                                }},
                                                            _args2.d_a1->v());
                                                      },
                                                      [](const typename tree::
                                                             Node &)
                                                          -> unsigned int {
                                                        return 0u;
                                                      }},
                                                  _args2.d_a0->v());
                                            }},
                                        t2->v());
                                  },
                                  [&](const typename tree::Node &)
                                      -> unsigned int {
                                    return std::visit(
                                        Overloaded{
                                            [&](const typename tree::Leaf
                                                    &_args2) -> unsigned int {
                                              return (_args0.d_a0 +
                                                      _args2.d_a0);
                                            },
                                            [](const typename tree::Node &)
                                                -> unsigned int { return 0u; }},
                                        t2->v());
                                  }},
                              _args.d_a1->v());
                        },
                        [](const typename tree::Node &) -> unsigned int {
                          return 0u;
                        }},
                    _args.d_a0->v());
              }},
          this->v());
    }

    __attribute__((pure)) unsigned int deep_match() const {
      return std::visit(Overloaded{[](const typename tree::Leaf &_args)
                                       -> unsigned int { return _args.d_a0; },
                                   [](const typename tree::Node &_args)
                                       -> unsigned int {
                                     return std::visit(Overloaded{[&](const typename tree::
                                                                          Leaf &
                                                                              _args0)
                                                                      -> unsigned int {
                                                                    return std::
                                                                        visit(
                                                                            Overloaded{
                                                                                [&](const typename tree::
                                                                                        Leaf &
                                                                                            _args1)
                                                                                    -> unsigned int {
                                                                                  return (
                                                                                      _args0
                                                                                          .d_a0 +
                                                                                      _args1
                                                                                          .d_a0);
                                                                                },
                                                                                [&](const typename tree::
                                                                                        Node &
                                                                                            _args1)
                                                                                    -> unsigned int {
                                                                                  return std::visit(Overloaded{[&](const typename tree::
                                                                                                                       Leaf &
                                                                                                                           _args2)
                                                                                                                   -> unsigned int {
                                                                                                                 return std::visit(
                                                                                                                     Overloaded{
                                                                                                                         [&](const typename tree::
                                                                                                                                 Leaf &
                                                                                                                                     _args3)
                                                                                                                             -> unsigned int {
                                                                                                                           return (
                                                                                                                               (_args0
                                                                                                                                    .d_a0 +
                                                                                                                                _args2
                                                                                                                                    .d_a0) +
                                                                                                                               _args3
                                                                                                                                   .d_a0);
                                                                                                                         },
                                                                                                                         [](const typename tree::
                                                                                                                                Node
                                                                                                                                    &)
                                                                                                                             -> unsigned int {
                                                                                                                           return 0u;
                                                                                                                         }},
                                                                                                                     _args1
                                                                                                                         .d_a1
                                                                                                                         ->v());
                                                                                                               },
                                                                                                               [](const typename tree::
                                                                                                                      Node
                                                                                                                          &)
                                                                                                                   -> unsigned int {
                                                                                                                 return 0u;
                                                                                                               }},
                                                                                                    _args1
                                                                                                        .d_a0
                                                                                                        ->v());
                                                                                }},
                                                                            _args
                                                                                .d_a1
                                                                                ->v());
                                                                  },
                                                                  [&](const typename tree::
                                                                          Node &
                                                                              _args0)
                                                                      -> unsigned int {
                                                                    return std::
                                                                        visit(
                                                                            Overloaded{
                                                                                [&](const typename tree::
                                                                                        Leaf &
                                                                                            _args1)
                                                                                    -> unsigned int {
                                                                                  return std::
                                                                                      visit(
                                                                                          Overloaded{
                                                                                              [&](const typename tree::
                                                                                                      Leaf &
                                                                                                          _args2)
                                                                                                  -> unsigned int {
                                                                                                return std::
                                                                                                    visit(Overloaded{
                                                                                                              [&](const typename tree::
                                                                                                                      Leaf &
                                                                                                                          _args3)
                                                                                                                  -> unsigned int {
                                                                                                                return (
                                                                                                                    (_args1
                                                                                                                         .d_a0 +
                                                                                                                     _args2
                                                                                                                         .d_a0) +
                                                                                                                    _args3
                                                                                                                        .d_a0);
                                                                                                              },
                                                                                                              [&](const typename tree::
                                                                                                                      Node
                                                                                                                          &
                                                                                                                              _args3) -> unsigned int {
                                                                                                                return std::visit(Overloaded{
                                                                                                                                      [&](const typename tree::Leaf &_args4) -> unsigned int {
                                                                                                                                        return std::visit(Overloaded{[&](const typename tree::Leaf
                                                                                                                                                                             &_args5) -> unsigned int {
                                                                                                                                                                       return (
                                                                                                                                                                           ((_args1
                                                                                                                                                                                 .d_a0 +
                                                                                                                                                                             _args2
                                                                                                                                                                                 .d_a0) +
                                                                                                                                                                            _args4
                                                                                                                                                                                .d_a0) +
                                                                                                                                                                           _args5
                                                                                                                                                                               .d_a0);
                                                                                                                                                                     },
                                                                                                                                                                     [](const typename tree::
                                                                                                                                                                            Node
                                                                                                                                                                                &)
                                                                                                                                                                         -> unsigned int {
                                                                                                                                                                       return 0u;
                                                                                                                                                                     }},
                                                                                                                                                          _args3
                                                                                                                                                              .d_a1
                                                                                                                                                              ->v());
                                                                                                                                      },
                                                                                                                                      [](const typename tree::
                                                                                                                                             Node
                                                                                                                                                 &)
                                                                                                                                          -> unsigned int {
                                                                                                                                        return 0u;
                                                                                                                                      }},
                                                                                                                                  _args3
                                                                                                                                      .d_a0
                                                                                                                                      ->v());
                                                                                                              }},
                                                                                                          _args
                                                                                                              .d_a1
                                                                                                              ->v());
                                                                                              },
                                                                                              [](const typename tree::
                                                                                                     Node
                                                                                                         &)
                                                                                                  -> unsigned int {
                                                                                                return 0u;
                                                                                              }},
                                                                                          _args0
                                                                                              .d_a1
                                                                                              ->v());
                                                                                },
                                                                                [&](const typename tree::
                                                                                        Node &
                                                                                            _args1)
                                                                                    -> unsigned int {
                                                                                  return std::
                                                                                      visit(
                                                                                          Overloaded{
                                                                                              [&](const typename tree::Leaf &_args2) -> unsigned int {
                                                                                                return std::visit(
                                                                                                    Overloaded{
                                                                                                        [&](const typename tree::
                                                                                                                Leaf &
                                                                                                                    _args3)
                                                                                                            -> unsigned int {
                                                                                                          return std::visit(Overloaded{[&](const typename tree::Leaf &_args4) -> unsigned int {
                                                                                                                                         return std::visit(Overloaded{[&](const typename tree::
                                                                                                                                                                              Leaf &
                                                                                                                                                                                  _args5)
                                                                                                                                                                          -> unsigned int {
                                                                                                                                                                        return (
                                                                                                                                                                            ((_args2
                                                                                                                                                                                  .d_a0 +
                                                                                                                                                                              _args3
                                                                                                                                                                                  .d_a0) +
                                                                                                                                                                             _args4
                                                                                                                                                                                 .d_a0) +
                                                                                                                                                                            _args5
                                                                                                                                                                                .d_a0);
                                                                                                                                                                      },
                                                                                                                                                                      [](const typename tree::
                                                                                                                                                                             Node
                                                                                                                                                                                 &)
                                                                                                                                                                          -> unsigned int {
                                                                                                                                                                        return 0u;
                                                                                                                                                                      }},
                                                                                                                                                           _args
                                                                                                                                                               .d_a1
                                                                                                                                                               ->v());
                                                                                                                                       },
                                                                                                                                       [](const typename tree::
                                                                                                                                              Node
                                                                                                                                                  &)
                                                                                                                                           -> unsigned int {
                                                                                                                                         return 0u;
                                                                                                                                       }},
                                                                                                                            _args0
                                                                                                                                .d_a1
                                                                                                                                ->v());
                                                                                                        },
                                                                                                        [](const typename tree::
                                                                                                               Node
                                                                                                                   &)
                                                                                                            -> unsigned int {
                                                                                                          return 0u;
                                                                                                        }},
                                                                                                    _args1
                                                                                                        .d_a1
                                                                                                        ->v());
                                                                                              },
                                                                                              [](const typename tree::
                                                                                                     Node
                                                                                                         &)
                                                                                                  -> unsigned int {
                                                                                                return 0u;
                                                                                              }},
                                                                                          _args1
                                                                                              .d_a0
                                                                                              ->v());
                                                                                }},
                                                                            _args0
                                                                                .d_a0
                                                                                ->v());
                                                                  }},
                                                       _args.d_a0->v());
                                   }},
                        this->v());
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<tree>, T1, std::shared_ptr<tree>, T1> F1>
    T1 tree_rec(F0 &&f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename tree::Leaf &_args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename tree::Node &_args) -> T1 {
                       return f0(_args.d_a0,
                                 _args.d_a0->template tree_rec<T1>(f, f0),
                                 _args.d_a1,
                                 _args.d_a1->template tree_rec<T1>(f, f0));
                     }},
          this->v());
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<tree>, T1, std::shared_ptr<tree>, T1> F1>
    T1 tree_rect(F0 &&f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename tree::Leaf &_args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename tree::Node &_args) -> T1 {
                       return f0(_args.d_a0,
                                 _args.d_a0->template tree_rect<T1>(f, f0),
                                 _args.d_a1,
                                 _args.d_a1->template tree_rect<T1>(f, f0));
                     }},
          this->v());
    }
  };

  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<list<t_A>> nil() {
      return std::make_shared<list<t_A>>(Nil{});
    }

    static std::shared_ptr<list<t_A>>
    cons(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), a1});
    }

    static std::shared_ptr<list<t_A>> cons(t_A a0,
                                           std::shared_ptr<list<t_A>> &&a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil &) -> T2 { return f; },
                   [&](const typename list<T1>::Cons &_args) -> T2 {
                     return f0(_args.d_a0, _args.d_a1,
                               list_rect<T1, T2>(f, f0, _args.d_a1));
                   }},
        l->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil &) -> T2 { return f; },
                   [&](const typename list<T1>::Cons &_args) -> T2 {
                     return f0(_args.d_a0, _args.d_a1,
                               list_rec<T1, T2>(f, f0, _args.d_a1));
                   }},
        l->v());
  }

  __attribute__((pure)) static unsigned int
  list_deep_match(const std::shared_ptr<list<std::shared_ptr<tree>>> &l);
  static std::shared_ptr<tree> as_pattern_test(std::shared_ptr<tree> t);
  static inline const unsigned int test1 =
      tree::node(tree::leaf(1u), tree::leaf(2u))->deep_match();
  static inline const unsigned int test2 =
      tree::leaf(5u)->multi_constructor(tree::leaf(10u));
};

#endif // INCLUDED_DEEP_PATTERN
