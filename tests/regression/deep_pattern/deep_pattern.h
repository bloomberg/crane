#ifndef INCLUDED_DEEP_PATTERN
#define INCLUDED_DEEP_PATTERN

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

    tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          const auto &_alt = std::get<Leaf>(_src->v());
          _dst->d_v_ = Leaf{_alt.d_a0};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ = Node{_alt.d_a0 ? std::make_unique<tree>() : nullptr,
                            _alt.d_a1 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf(unsigned int a0) { return tree(Leaf{std::move(a0)}); }

    static tree node(tree a0, tree a1) {
      return tree(Node{std::make_unique<tree>(std::move(a0)),
                       std::make_unique<tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack;
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int nested_let_match() const {
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

    unsigned int conditional_match(const unsigned int &target) const {
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

    bool has_value(const unsigned int &target) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<typename tree::Leaf>(_sv.v());
        return d_a0 == target;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename tree::Node>(_sv.v());
        return ((*(d_a0)).has_value(target) || (*(d_a1)).has_value(target));
      }
    }

    tree as_pattern_test() const { return std::move(*(this)); }

    unsigned int wildcard_with_bindings() const {
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

    unsigned int multi_constructor(const tree &t2) const {
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

    unsigned int deep_match() const {
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

    list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    list clone() const {
      list _out{};

      struct _CloneFrame {
        const list *_src;
        list *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const list *_src = _frame._src;
        list *_dst = _frame._dst;
        if (std::holds_alternative<Nil>(_src->v())) {
          const auto &_alt = std::get<Nil>(_src->v());
          _dst->d_v_ = Nil{};
        } else {
          const auto &_alt = std::get<Cons>(_src->v());
          _dst->d_v_ =
              Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<list>() : nullptr};
          auto &_dst_alt = std::get<Cons>(_dst->d_v_);
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
      return _out;
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

    static list<t_A> nil() { return list(Nil{}); }

    static list<t_A> cons(t_A a0, list<t_A> a1) {
      return list(
          Cons{std::move(a0), std::make_unique<list<t_A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::unique_ptr<list>> _stack;
      auto _drain = [&](list &_node) {
        if (std::holds_alternative<Cons>(_node.d_v_)) {
          auto &_alt = std::get<Cons>(_node.d_v_);
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

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

  static unsigned int list_deep_match(const list<tree> &l);
  static inline const unsigned int test1 =
      tree::node(tree::leaf(1u), tree::leaf(2u)).deep_match();
  static inline const unsigned int test2 =
      tree::leaf(5u).multi_constructor(tree::leaf(10u));
};

#endif // INCLUDED_DEEP_PATTERN
