#ifndef INCLUDED_ARENA_INTEROP
#define INCLUDED_ARENA_INTEROP

#include "arena.h"
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat add(Nat m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      const auto &[a0] = std::get<typename Nat::S>(this->v());
      return Nat::s(a0->add(std::move(m)));
    }
  }
};

struct Interop {
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      tree<A> *t1;
      A x;
      tree<A> *t2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    tree(const tree<A> &_other) {
      if (std::holds_alternative<typename tree<A>::Leaf>(_other.v())) {
        this->v_ = Leaf{};
      } else {
        const auto &[t1, x, t2] = std::get<typename tree<A>::Node>(_other.v());
        this->v_ = Node{crane::arena_alloc<tree<A>>(*t1), x,
                        crane::arena_alloc<tree<A>>(*t2)};
      }
    }

    // MANIPULATORS
    tree<A> &operator=(const tree<A> &_other) {
      if (&*this != &_other) {
        tree<A> _tmp = tree<A>(_other);
        this->v_ = std::move(_tmp.v_mut());
      }
      return *this;
    }

    // CREATORS
    static tree<A> leaf() { return tree(Leaf{}); }

    static tree<A> node(crane::arena &a, tree<A> t1, A x, tree<A> t2) {
      return tree(Node{a.alloc<tree<A>>(std::move(t1)), std::move(x),
                       a.alloc<tree<A>>(std::move(t2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Nat count() const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return Nat::s(Nat::o());
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        return Nat::s(Nat::o()).add(a0->count()).add(a2->count());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree<A> &, T1 &, A &, tree<A> &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        return f0(*a0, a0->template tree_rec<T1>(f, f0), a1, *a2,
                  a2->template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree<A> &, T1 &, A &, tree<A> &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree<A>::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(this->v());
        return f0(*a0, a0->template tree_rect<T1>(f, f0), a1, *a2,
                  a2->template tree_rect<T1>(f, f0));
      }
    }
  };

  struct nlist {
    // TYPES
    struct Nnil {};

    struct Ncons {
      Nat a0;
      std::shared_ptr<nlist> a1;
    };

    using variant_t = std::variant<Nnil, Ncons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    nlist() {}

    explicit nlist(Nnil _v) : v_(_v) {}

    explicit nlist(Ncons _v) : v_(std::move(_v)) {}

    static nlist nnil() { return nlist(Nnil{}); }

    static nlist ncons(Nat a0, nlist a1) {
      return nlist(
          Ncons{std::move(a0), std::make_shared<nlist>(std::move(a1))});
    }

    // MANIPULATORS
    ~nlist() {
      std::vector<std::shared_ptr<nlist>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Ncons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Nat nlist_len() const {
      if (std::holds_alternative<typename nlist::Nnil>(this->v())) {
        return Nat::o();
      } else {
        const auto &[a0, a1] = std::get<typename nlist::Ncons>(this->v());
        return Nat::s(Nat::o()).add(a1->nlist_len());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, Nat &, nlist &, T1 &>
    T1 nlist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename nlist::Nnil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename nlist::Ncons>(this->v());
        return f0(a0, *a1, a1->template nlist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, Nat &, nlist &, T1 &>
    T1 nlist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename nlist::Nnil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename nlist::Ncons>(this->v());
        return f0(a0, *a1, a1->template nlist_rect<T1>(f, f0));
      }
    }
  };

  struct wrapper {
    Nat w_id;
    tree<Nat> w_tree;
  };

  static Nat wrapper_size(const wrapper &w);
};

#endif // INCLUDED_ARENA_INTEROP
