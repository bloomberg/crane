#ifndef INCLUDED_DEEP_PATTERN
#define INCLUDED_DEEP_PATTERN

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct DeepPattern {
  struct tree {
    // TYPES
    struct Leaf {
      uint64_t a0;
    };

    struct Node {
      std::shared_ptr<tree> a0;
      std::shared_ptr<tree> a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(std::move(_v)) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf(uint64_t a0) { return tree(Leaf{a0}); }

    static tree node(tree a0, tree a1) {
      return tree(Node{std::make_shared<tree>(std::move(a0)),
                       std::make_shared<tree>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t nested_let_match() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        uint64_t a = [&]() {
          auto &&_sv0 = *a0;
          if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
            const auto &[a00] = std::get<typename tree::Leaf>(_sv0.v());
            return a00;
          } else {
            return UINT64_C(0);
          }
        }();
        uint64_t b = [&]() {
          auto &&_sv1 = *a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            return a01;
          } else {
            return UINT64_C(0);
          }
        }();
        uint64_t c = (a + b);
        uint64_t d = (c * UINT64_C(2));
        return (d + UINT64_C(1));
      }
    }

    uint64_t conditional_match(uint64_t target) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        if (a0 == target) {
          return UINT64_C(100);
        } else {
          return a0;
        }
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        if (this->has_value(target)) {
          return UINT64_C(200);
        } else {
          auto &&_sv0 = *a0;
          if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
            const auto &[a00] = std::get<typename tree::Leaf>(_sv0.v());
            return a00;
          } else {
            return UINT64_C(0);
          }
        }
      }
    }

    bool has_value(uint64_t target) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        return a0 == target;
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        return (a0->has_value(target) || a1->has_value(target));
      }
    }

    tree as_pattern_test() const { return std::move(*this); }

    uint64_t wildcard_with_bindings() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        uint64_t x = [&]() {
          auto &&_sv0 = *a0;
          if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
            const auto &[a00] = std::get<typename tree::Leaf>(_sv0.v());
            return a00;
          } else {
            return UINT64_C(0);
          }
        }();
        uint64_t y = [&]() {
          auto &&_sv1 = *a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            return a01;
          } else {
            return UINT64_C(0);
          }
        }();
        return (x + y);
      }
    }

    uint64_t multi_constructor(const tree &t2) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
          const auto &[a00] = std::get<typename tree::Leaf>(t2.v());
          return (a0 + a00);
        } else {
          const auto &[a00, a10] = std::get<typename tree::Node>(t2.v());
          auto &&_sv1 = *a00;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            return (a0 + a01);
          } else {
            return UINT64_C(0);
          }
        }
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          const auto &[a00] = std::get<typename tree::Leaf>(_sv0.v());
          auto &&_sv1 = *a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
              const auto &[a02] = std::get<typename tree::Leaf>(t2.v());
              return (a00 + a02);
            } else {
              const auto &[a02, a12] = std::get<typename tree::Node>(t2.v());
              auto &&_sv3 = *a02;
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[a03] = std::get<typename tree::Leaf>(_sv3.v());
                auto &&_sv4 = *a12;
                if (std::holds_alternative<typename tree::Leaf>(_sv4.v())) {
                  const auto &[a04] = std::get<typename tree::Leaf>(_sv4.v());
                  return (((a00 + a01) + a03) + a04);
                } else {
                  return UINT64_C(0);
                }
              } else {
                return UINT64_C(0);
              }
            }
          } else {
            if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
              const auto &[a02] = std::get<typename tree::Leaf>(t2.v());
              return (a00 + a02);
            } else {
              return UINT64_C(0);
            }
          }
        } else {
          return UINT64_C(0);
        }
      }
    }

    uint64_t deep_match() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        return a0;
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          const auto &[a00] = std::get<typename tree::Leaf>(_sv0.v());
          auto &&_sv1 = *a1;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            return (a00 + a01);
          } else {
            const auto &[a01, a11] = std::get<typename tree::Node>(_sv1.v());
            auto &&_sv2 = *a01;
            if (std::holds_alternative<typename tree::Leaf>(_sv2.v())) {
              const auto &[a02] = std::get<typename tree::Leaf>(_sv2.v());
              auto &&_sv3 = *a11;
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[a03] = std::get<typename tree::Leaf>(_sv3.v());
                return ((a00 + a02) + a03);
              } else {
                return UINT64_C(0);
              }
            } else {
              return UINT64_C(0);
            }
          }
        } else {
          const auto &[a00, a10] = std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *a00;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[a01] = std::get<typename tree::Leaf>(_sv1.v());
            auto &&_sv2 = *a10;
            if (std::holds_alternative<typename tree::Leaf>(_sv2.v())) {
              const auto &[a02] = std::get<typename tree::Leaf>(_sv2.v());
              auto &&_sv3 = *a1;
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[a03] = std::get<typename tree::Leaf>(_sv3.v());
                return ((a01 + a02) + a03);
              } else {
                const auto &[a03, a13] =
                    std::get<typename tree::Node>(_sv3.v());
                auto &&_sv4 = *a03;
                if (std::holds_alternative<typename tree::Leaf>(_sv4.v())) {
                  const auto &[a04] = std::get<typename tree::Leaf>(_sv4.v());
                  auto &&_sv5 = *a13;
                  if (std::holds_alternative<typename tree::Leaf>(_sv5.v())) {
                    const auto &[a05] = std::get<typename tree::Leaf>(_sv5.v());
                    return (((a01 + a02) + a04) + a05);
                  } else {
                    return UINT64_C(0);
                  }
                } else {
                  return UINT64_C(0);
                }
              }
            } else {
              return UINT64_C(0);
            }
          } else {
            const auto &[a01, a11] = std::get<typename tree::Node>(_sv1.v());
            auto &&_sv2 = *a01;
            if (std::holds_alternative<typename tree::Leaf>(_sv2.v())) {
              const auto &[a02] = std::get<typename tree::Leaf>(_sv2.v());
              auto &&_sv3 = *a11;
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[a03] = std::get<typename tree::Leaf>(_sv3.v());
                auto &&_sv4 = *a10;
                if (std::holds_alternative<typename tree::Leaf>(_sv4.v())) {
                  const auto &[a04] = std::get<typename tree::Leaf>(_sv4.v());
                  auto &&_sv5 = *a1;
                  if (std::holds_alternative<typename tree::Leaf>(_sv5.v())) {
                    const auto &[a05] = std::get<typename tree::Leaf>(_sv5.v());
                    return (((a02 + a03) + a04) + a05);
                  } else {
                    return UINT64_C(0);
                  }
                } else {
                  return UINT64_C(0);
                }
              } else {
                return UINT64_C(0);
              }
            } else {
              return UINT64_C(0);
            }
          }
        }
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, tree &, T1 &, tree &, T1 &>
    T1 tree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rec<T1>(f, f0), *a1,
                  a1->template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, tree &, T1 &, tree &, T1 &>
    T1 tree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        const auto &[a0] = std::get<typename tree::Leaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rect<T1>(f, f0), *a1,
                  a1->template tree_rect<T1>(f, f0));
      }
    }
  };

  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<list<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<list<A>>(*a1) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list(
          Cons{std::move(a0), std::make_shared<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, list<A> &, T1 &>
    T1 list_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename list<A>::Nil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename list<A>::Cons>(this->v());
        return f0(a0, *a1, a1->template list_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, list<A> &, T1 &>
    T1 list_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename list<A>::Nil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename list<A>::Cons>(this->v());
        return f0(a0, *a1, a1->template list_rect<T1>(f, f0));
      }
    }
  };

  static uint64_t list_deep_match(const list<tree> &l);
  static inline const uint64_t test1 =
      tree::node(tree::leaf(UINT64_C(1)), tree::leaf(UINT64_C(2))).deep_match();
  static inline const uint64_t test2 =
      tree::leaf(UINT64_C(5)).multi_constructor(tree::leaf(UINT64_C(10)));
};

#endif // INCLUDED_DEEP_PATTERN
