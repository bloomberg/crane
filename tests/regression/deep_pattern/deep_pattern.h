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
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &_m = *std::get_if<typename tree::Leaf>(&this->v());
        return _m.d_a0;
      } else {
        const auto &_m = *std::get_if<typename tree::Node>(&this->v());
        unsigned int a = [&]() {
          auto &&_sv0 = _m.d_a0;
          if (std::holds_alternative<typename tree::Leaf>(_sv0->v())) {
            const auto &_m0 = *std::get_if<typename tree::Leaf>(&_sv0->v());
            return _m0.d_a0;
          } else {
            return 0u;
          }
        }();
        unsigned int b = [&]() {
          auto &&_sv1 = _m.d_a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1->v())) {
            const auto &_m1 = *std::get_if<typename tree::Leaf>(&_sv1->v());
            return _m1.d_a0;
          } else {
            return 0u;
          }
        }();
        unsigned int c = (a + b);
        unsigned int d = (c * 2u);
        return (d + 1u);
      }
    }

    __attribute__((pure)) unsigned int
    conditional_match(const unsigned int target) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &_m = *std::get_if<typename tree::Leaf>(&this->v());
        if (_m.d_a0 == target) {
          return 100u;
        } else {
          return _m.d_a0;
        }
      } else {
        const auto &_m = *std::get_if<typename tree::Node>(&this->v());
        if (this->has_value(target)) {
          return 200u;
        } else {
          auto &&_sv0 = _m.d_a0;
          if (std::holds_alternative<typename tree::Leaf>(_sv0->v())) {
            const auto &_m0 = *std::get_if<typename tree::Leaf>(&_sv0->v());
            return _m0.d_a0;
          } else {
            return 0u;
          }
        }
      }
    }

    __attribute__((pure)) bool has_value(const unsigned int target) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &_m = *std::get_if<typename tree::Leaf>(&this->v());
        return _m.d_a0 == target;
      } else {
        const auto &_m = *std::get_if<typename tree::Node>(&this->v());
        return (_m.d_a0->has_value(target) || _m.d_a1->has_value(target));
      }
    }

    __attribute__((pure)) unsigned int wildcard_with_bindings() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &_m = *std::get_if<typename tree::Leaf>(&this->v());
        return _m.d_a0;
      } else {
        const auto &_m = *std::get_if<typename tree::Node>(&this->v());
        unsigned int x = [&]() {
          auto &&_sv0 = _m.d_a0;
          if (std::holds_alternative<typename tree::Leaf>(_sv0->v())) {
            const auto &_m0 = *std::get_if<typename tree::Leaf>(&_sv0->v());
            return _m0.d_a0;
          } else {
            return 0u;
          }
        }();
        unsigned int y = [&]() {
          auto &&_sv1 = _m.d_a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1->v())) {
            const auto &_m1 = *std::get_if<typename tree::Leaf>(&_sv1->v());
            return _m1.d_a0;
          } else {
            return 0u;
          }
        }();
        return (x + y);
      }
    }

    __attribute__((pure)) unsigned int
    multi_constructor(const std::shared_ptr<tree> &t2) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &_m = *std::get_if<typename tree::Leaf>(&this->v());
        if (std::holds_alternative<typename tree::Leaf>(t2->v())) {
          const auto &_m0 = *std::get_if<typename tree::Leaf>(&t2->v());
          return (_m.d_a0 + _m0.d_a0);
        } else {
          const auto &_m0 = *std::get_if<typename tree::Node>(&t2->v());
          auto &&_sv1 = _m0.d_a0;
          if (std::holds_alternative<typename tree::Leaf>(_sv1->v())) {
            const auto &_m1 = *std::get_if<typename tree::Leaf>(&_sv1->v());
            return (_m.d_a0 + _m1.d_a0);
          } else {
            return 0u;
          }
        }
      } else {
        const auto &_m = *std::get_if<typename tree::Node>(&this->v());
        auto &&_sv0 = _m.d_a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0->v())) {
          const auto &_m0 = *std::get_if<typename tree::Leaf>(&_sv0->v());
          auto &&_sv1 = _m.d_a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1->v())) {
            const auto &_m1 = *std::get_if<typename tree::Leaf>(&_sv1->v());
            if (std::holds_alternative<typename tree::Leaf>(t2->v())) {
              const auto &_m2 = *std::get_if<typename tree::Leaf>(&t2->v());
              return (_m0.d_a0 + _m2.d_a0);
            } else {
              const auto &_m2 = *std::get_if<typename tree::Node>(&t2->v());
              auto &&_sv3 = _m2.d_a0;
              if (std::holds_alternative<typename tree::Leaf>(_sv3->v())) {
                const auto &_m3 = *std::get_if<typename tree::Leaf>(&_sv3->v());
                auto &&_sv4 = _m2.d_a1;
                if (std::holds_alternative<typename tree::Leaf>(_sv4->v())) {
                  const auto &_m4 =
                      *std::get_if<typename tree::Leaf>(&_sv4->v());
                  return (((_m0.d_a0 + _m1.d_a0) + _m3.d_a0) + _m4.d_a0);
                } else {
                  return 0u;
                }
              } else {
                return 0u;
              }
            }
          } else {
            if (std::holds_alternative<typename tree::Leaf>(t2->v())) {
              const auto &_m2 = *std::get_if<typename tree::Leaf>(&t2->v());
              return (_m0.d_a0 + _m2.d_a0);
            } else {
              return 0u;
            }
          }
        } else {
          return 0u;
        }
      }
    }

    __attribute__((pure)) unsigned int deep_match() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &_m = *std::get_if<typename tree::Leaf>(&this->v());
        return _m.d_a0;
      } else {
        const auto &_m = *std::get_if<typename tree::Node>(&this->v());
        auto &&_sv0 = _m.d_a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0->v())) {
          const auto &_m0 = *std::get_if<typename tree::Leaf>(&_sv0->v());
          auto &&_sv1 = _m.d_a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1->v())) {
            const auto &_m1 = *std::get_if<typename tree::Leaf>(&_sv1->v());
            return (_m0.d_a0 + _m1.d_a0);
          } else {
            const auto &_m1 = *std::get_if<typename tree::Node>(&_sv1->v());
            auto &&_sv2 = _m1.d_a0;
            if (std::holds_alternative<typename tree::Leaf>(_sv2->v())) {
              const auto &_m2 = *std::get_if<typename tree::Leaf>(&_sv2->v());
              auto &&_sv3 = _m1.d_a1;
              if (std::holds_alternative<typename tree::Leaf>(_sv3->v())) {
                const auto &_m3 = *std::get_if<typename tree::Leaf>(&_sv3->v());
                return ((_m0.d_a0 + _m2.d_a0) + _m3.d_a0);
              } else {
                return 0u;
              }
            } else {
              return 0u;
            }
          }
        } else {
          const auto &_m0 = *std::get_if<typename tree::Node>(&_sv0->v());
          auto &&_sv1 = _m0.d_a0;
          if (std::holds_alternative<typename tree::Leaf>(_sv1->v())) {
            const auto &_m1 = *std::get_if<typename tree::Leaf>(&_sv1->v());
            auto &&_sv2 = _m0.d_a1;
            if (std::holds_alternative<typename tree::Leaf>(_sv2->v())) {
              const auto &_m2 = *std::get_if<typename tree::Leaf>(&_sv2->v());
              auto &&_sv3 = _m.d_a1;
              if (std::holds_alternative<typename tree::Leaf>(_sv3->v())) {
                const auto &_m3 = *std::get_if<typename tree::Leaf>(&_sv3->v());
                return ((_m1.d_a0 + _m2.d_a0) + _m3.d_a0);
              } else {
                const auto &_m3 = *std::get_if<typename tree::Node>(&_sv3->v());
                auto &&_sv4 = _m3.d_a0;
                if (std::holds_alternative<typename tree::Leaf>(_sv4->v())) {
                  const auto &_m4 =
                      *std::get_if<typename tree::Leaf>(&_sv4->v());
                  auto &&_sv5 = _m3.d_a1;
                  if (std::holds_alternative<typename tree::Leaf>(_sv5->v())) {
                    const auto &_m5 =
                        *std::get_if<typename tree::Leaf>(&_sv5->v());
                    return (((_m1.d_a0 + _m2.d_a0) + _m4.d_a0) + _m5.d_a0);
                  } else {
                    return 0u;
                  }
                } else {
                  return 0u;
                }
              }
            } else {
              return 0u;
            }
          } else {
            const auto &_m1 = *std::get_if<typename tree::Node>(&_sv1->v());
            auto &&_sv2 = _m1.d_a0;
            if (std::holds_alternative<typename tree::Leaf>(_sv2->v())) {
              const auto &_m2 = *std::get_if<typename tree::Leaf>(&_sv2->v());
              auto &&_sv3 = _m1.d_a1;
              if (std::holds_alternative<typename tree::Leaf>(_sv3->v())) {
                const auto &_m3 = *std::get_if<typename tree::Leaf>(&_sv3->v());
                auto &&_sv4 = _m0.d_a1;
                if (std::holds_alternative<typename tree::Leaf>(_sv4->v())) {
                  const auto &_m4 =
                      *std::get_if<typename tree::Leaf>(&_sv4->v());
                  auto &&_sv5 = _m.d_a1;
                  if (std::holds_alternative<typename tree::Leaf>(_sv5->v())) {
                    const auto &_m5 =
                        *std::get_if<typename tree::Leaf>(&_sv5->v());
                    return (((_m2.d_a0 + _m3.d_a0) + _m4.d_a0) + _m5.d_a0);
                  } else {
                    return 0u;
                  }
                } else {
                  return 0u;
                }
              } else {
                return 0u;
              }
            } else {
              return 0u;
            }
          }
        }
      }
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<tree>, T1, std::shared_ptr<tree>, T1> F1>
    T1 tree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &_m = *std::get_if<typename tree::Leaf>(&this->v());
        return f(_m.d_a0);
      } else {
        const auto &_m = *std::get_if<typename tree::Node>(&this->v());
        return f0(_m.d_a0, _m.d_a0->template tree_rec<T1>(f, f0), _m.d_a1,
                  _m.d_a1->template tree_rec<T1>(f, f0));
      }
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<tree>, T1, std::shared_ptr<tree>, T1> F1>
    T1 tree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &_m = *std::get_if<typename tree::Leaf>(&this->v());
        return f(_m.d_a0);
      } else {
        const auto &_m = *std::get_if<typename tree::Node>(&this->v());
        return f0(_m.d_a0, _m.d_a0->template tree_rect<T1>(f, f0), _m.d_a1,
                  _m.d_a1->template tree_rect<T1>(f, f0));
      }
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
    if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
      return f;
    } else {
      const auto &_m = *std::get_if<typename list<T1>::Cons>(&l->v());
      return f0(_m.d_a0, _m.d_a1, list_rect<T1, T2>(f, f0, _m.d_a1));
    }
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
      return f;
    } else {
      const auto &_m = *std::get_if<typename list<T1>::Cons>(&l->v());
      return f0(_m.d_a0, _m.d_a1, list_rec<T1, T2>(f, f0, _m.d_a1));
    }
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
