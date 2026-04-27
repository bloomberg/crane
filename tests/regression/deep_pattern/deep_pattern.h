#ifndef INCLUDED_DEEP_PATTERN
#define INCLUDED_DEEP_PATTERN

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct DeepPattern {
  struct tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      std::unique_ptr<tree> d_a0;
      std::unique_ptr<tree> d_a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    tree(const tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return tree(Leaf{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<Node>(_sv.v());
        return tree(Node{
            d_a0 ? std::make_unique<DeepPattern::tree>(d_a0->clone()) : nullptr,
            d_a1 ? std::make_unique<DeepPattern::tree>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf(unsigned int a0) {
      return tree(Leaf{std::move(a0)});
    }

    __attribute__((pure)) static tree node(const tree &a0, const tree &a1) {
      return tree(Node{std::make_unique<tree>(a0), std::make_unique<tree>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree *operator->() { return this; }

    __attribute__((pure)) const tree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int nested_let_match() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename tree::Leaf>(_sv.v());
        return d_a0;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename tree::Node>(_sv.v());
        unsigned int a = [&]() {
          auto &&_sv0 = *(d_a0);
          if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
            const auto &[d_a00] = std::get<typename tree::Leaf>(_sv0.v());
            return d_a00;
          } else {
            return 0u;
          }
        }();
        unsigned int b = [&]() {
          auto &&_sv1 = *(d_a1);
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename tree::Leaf>(_sv1.v());
            return d_a01;
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
    conditional_match(const unsigned int &target) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename tree::Leaf>(_sv.v());
        if (d_a0 == target) {
          return 100u;
        } else {
          return d_a0;
        }
      } else {
        const auto &[d_a0, d_a1] = std::get<typename tree::Node>(_sv.v());
        if ((*(this)).has_value(target)) {
          return 200u;
        } else {
          auto &&_sv0 = *(d_a0);
          if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
            const auto &[d_a00] = std::get<typename tree::Leaf>(_sv0.v());
            return d_a00;
          } else {
            return 0u;
          }
        }
      }
    }

    __attribute__((pure)) bool has_value(const unsigned int &target) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename tree::Leaf>(_sv.v());
        return d_a0 == target;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename tree::Node>(_sv.v());
        return ((*(d_a0)).has_value(target) || (*(d_a1)).has_value(target));
      }
    }

    __attribute__((pure)) tree as_pattern_test() const { return *(this); }

    __attribute__((pure)) unsigned int wildcard_with_bindings() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename tree::Leaf>(_sv.v());
        return d_a0;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename tree::Node>(_sv.v());
        unsigned int x = [&]() {
          auto &&_sv0 = *(d_a0);
          if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
            const auto &[d_a00] = std::get<typename tree::Leaf>(_sv0.v());
            return d_a00;
          } else {
            return 0u;
          }
        }();
        unsigned int y = [&]() {
          auto &&_sv1 = *(d_a1);
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename tree::Leaf>(_sv1.v());
            return d_a01;
          } else {
            return 0u;
          }
        }();
        return (x + y);
      }
    }

    __attribute__((pure)) unsigned int multi_constructor(const tree &t2) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename tree::Leaf>(_sv.v());
        if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
          const auto &[d_a00] = std::get<typename tree::Leaf>(t2.v());
          return (d_a0 + d_a00);
        } else {
          const auto &[d_a00, d_a10] = std::get<typename tree::Node>(t2.v());
          auto &&_sv1 = *(d_a00);
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename tree::Leaf>(_sv1.v());
            return (d_a0 + d_a01);
          } else {
            return 0u;
          }
        }
      } else {
        const auto &[d_a0, d_a1] = std::get<typename tree::Node>(_sv.v());
        auto &&_sv0 = *(d_a0);
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          const auto &[d_a00] = std::get<typename tree::Leaf>(_sv0.v());
          auto &&_sv1 = *(d_a1);
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename tree::Leaf>(_sv1.v());
            if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
              const auto &[d_a02] = std::get<typename tree::Leaf>(t2.v());
              return (d_a00 + d_a02);
            } else {
              const auto &[d_a02, d_a12] =
                  std::get<typename tree::Node>(t2.v());
              auto &&_sv3 = *(d_a02);
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[d_a03] = std::get<typename tree::Leaf>(_sv3.v());
                auto &&_sv4 = *(d_a12);
                if (std::holds_alternative<typename tree::Leaf>(_sv4.v())) {
                  const auto &[d_a04] = std::get<typename tree::Leaf>(_sv4.v());
                  return (((d_a00 + d_a01) + d_a03) + d_a04);
                } else {
                  return 0u;
                }
              } else {
                return 0u;
              }
            }
          } else {
            if (std::holds_alternative<typename tree::Leaf>(t2.v())) {
              const auto &[d_a02] = std::get<typename tree::Leaf>(t2.v());
              return (d_a00 + d_a02);
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
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename tree::Leaf>(_sv.v());
        return d_a0;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename tree::Node>(_sv.v());
        auto &&_sv0 = *(d_a0);
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          const auto &[d_a00] = std::get<typename tree::Leaf>(_sv0.v());
          auto &&_sv1 = *(d_a1);
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename tree::Leaf>(_sv1.v());
            return (d_a00 + d_a01);
          } else {
            const auto &[d_a01, d_a11] =
                std::get<typename tree::Node>(_sv1.v());
            auto &&_sv2 = *(d_a01);
            if (std::holds_alternative<typename tree::Leaf>(_sv2.v())) {
              const auto &[d_a02] = std::get<typename tree::Leaf>(_sv2.v());
              auto &&_sv3 = *(d_a11);
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[d_a03] = std::get<typename tree::Leaf>(_sv3.v());
                return ((d_a00 + d_a02) + d_a03);
              } else {
                return 0u;
              }
            } else {
              return 0u;
            }
          }
        } else {
          const auto &[d_a00, d_a10] = std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *(d_a00);
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename tree::Leaf>(_sv1.v());
            auto &&_sv2 = *(d_a10);
            if (std::holds_alternative<typename tree::Leaf>(_sv2.v())) {
              const auto &[d_a02] = std::get<typename tree::Leaf>(_sv2.v());
              auto &&_sv3 = *(d_a1);
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[d_a03] = std::get<typename tree::Leaf>(_sv3.v());
                return ((d_a01 + d_a02) + d_a03);
              } else {
                const auto &[d_a03, d_a13] =
                    std::get<typename tree::Node>(_sv3.v());
                auto &&_sv4 = *(d_a03);
                if (std::holds_alternative<typename tree::Leaf>(_sv4.v())) {
                  const auto &[d_a04] = std::get<typename tree::Leaf>(_sv4.v());
                  auto &&_sv5 = *(d_a13);
                  if (std::holds_alternative<typename tree::Leaf>(_sv5.v())) {
                    const auto &[d_a05] =
                        std::get<typename tree::Leaf>(_sv5.v());
                    return (((d_a01 + d_a02) + d_a04) + d_a05);
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
            const auto &[d_a01, d_a11] =
                std::get<typename tree::Node>(_sv1.v());
            auto &&_sv2 = *(d_a01);
            if (std::holds_alternative<typename tree::Leaf>(_sv2.v())) {
              const auto &[d_a02] = std::get<typename tree::Leaf>(_sv2.v());
              auto &&_sv3 = *(d_a11);
              if (std::holds_alternative<typename tree::Leaf>(_sv3.v())) {
                const auto &[d_a03] = std::get<typename tree::Leaf>(_sv3.v());
                auto &&_sv4 = *(d_a10);
                if (std::holds_alternative<typename tree::Leaf>(_sv4.v())) {
                  const auto &[d_a04] = std::get<typename tree::Leaf>(_sv4.v());
                  auto &&_sv5 = *(d_a1);
                  if (std::holds_alternative<typename tree::Leaf>(_sv5.v())) {
                    const auto &[d_a05] =
                        std::get<typename tree::Leaf>(_sv5.v());
                    return (((d_a02 + d_a03) + d_a04) + d_a05);
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

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, tree, T1, tree, T1> F1>
    T1 tree_rec(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename tree::Leaf>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0, d_a1] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rec<T1>(f, f0), *(d_a1),
                  (*(d_a1)).template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, tree, T1, tree, T1> F1>
    T1 tree_rect(F0 &&f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename tree::Leaf>(_sv.v());
        return f(d_a0);
      } else {
        const auto &[d_a0, d_a1] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rect<T1>(f, f0), *(d_a1),
                  (*(d_a1)).template tree_rect<T1>(f, f0));
      }
    }
  };

  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    list(const list<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    list(list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) list<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<t_A>(Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return list<t_A>(Cons{
            d_a0, d_a1 ? std::make_unique<DeepPattern::list<t_A>>(d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        d_v_ = Nil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<_U>::Cons>(_other.v());
        d_v_ = Cons{t_A(d_a0),
                    d_a1 ? std::make_unique<list<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static list<t_A> nil() { return list(Nil{}); }

    __attribute__((pure)) static list<t_A> cons(t_A a0, const list<t_A> &a1) {
      return list(Cons{std::move(a0), std::make_unique<list<t_A>>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) list<t_A> *operator->() { return this; }

    __attribute__((pure)) const list<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = list<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A, list<t_A>, T1> F1>
    T1 list_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename list<t_A>::Nil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename list<t_A>::Cons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template list_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, t_A, list<t_A>, T1> F1>
    T1 list_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename list<t_A>::Nil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename list<t_A>::Cons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template list_rect<T1>(f, f0));
      }
    }
  };

  __attribute__((pure)) static unsigned int
  list_deep_match(const list<tree> &l);
  static inline const unsigned int test1 =
      tree::node(tree::leaf(1u), tree::leaf(2u)).deep_match();
  static inline const unsigned int test2 =
      tree::leaf(5u).multi_constructor(tree::leaf(10u));
};

#endif // INCLUDED_DEEP_PATTERN
