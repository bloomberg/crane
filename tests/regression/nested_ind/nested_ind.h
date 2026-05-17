#ifndef INCLUDED_NESTED_IND
#define INCLUDED_NESTED_IND

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, (*a1).app(std::move(m)));
    }
  }
};

struct NestedInd {
  template <typename A> struct custom_list {
    // TYPES
    struct Cnil {};

    struct Ccons {
      A a0;
      std::unique_ptr<custom_list<A>> a1;
    };

    using variant_t = std::variant<Cnil, Ccons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    custom_list() {}

    explicit custom_list(Cnil _v) : v_(_v) {}

    explicit custom_list(Ccons _v) : v_(std::move(_v)) {}

    custom_list(const custom_list<A> &_other)
        : v_(std::move(_other.clone().v_)) {}

    custom_list(custom_list<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    custom_list<A> &operator=(const custom_list<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    custom_list<A> &operator=(custom_list<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    custom_list<A> clone() const {
      custom_list<A> _out{};

      struct _CloneFrame {
        const custom_list<A> *_src;
        custom_list<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const custom_list<A> *_src = _frame._src;
        custom_list<A> *_dst = _frame._dst;
        if (std::holds_alternative<Cnil>(_src->v())) {
          _dst->v_ = Cnil{};
        } else {
          const auto &_alt = std::get<Ccons>(_src->v());
          _dst->v_ = Ccons{_alt.a0, _alt.a1 ? std::make_unique<custom_list<A>>()
                                            : nullptr};
          auto &_dst_alt = std::get<Ccons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit custom_list(const custom_list<_U> &_other) {
      if (std::holds_alternative<typename custom_list<_U>::Cnil>(_other.v())) {
        this->v_ = Cnil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename custom_list<_U>::Ccons>(_other.v());
        this->v_ =
            Ccons{A(a0), a1 ? std::make_unique<custom_list<A>>(*a1) : nullptr};
      }
    }

    static custom_list<A> cnil() { return custom_list(Cnil{}); }

    static custom_list<A> ccons(A a0, custom_list<A> a1) {
      return custom_list(Ccons{
          std::move(a0), std::make_unique<custom_list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~custom_list() {
      std::vector<std::unique_ptr<custom_list<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](custom_list<A> &_node) {
        if (std::holds_alternative<Ccons>(_node.v_)) {
          auto &_alt = std::get<Ccons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    unsigned int custom_list_length() const {
      if (std::holds_alternative<typename custom_list<A>::Cnil>(this->v())) {
        return 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename custom_list<A>::Ccons>(this->v());
        return (1u + (*a1).custom_list_length());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, custom_list<A> &, T1 &>
    T1 custom_list_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename custom_list<A>::Cnil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] =
            std::get<typename custom_list<A>::Ccons>(this->v());
        return f0(a0, *a1, (*a1).template custom_list_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, custom_list<A> &, T1 &>
    T1 custom_list_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename custom_list<A>::Cnil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] =
            std::get<typename custom_list<A>::Ccons>(this->v());
        return f0(a0, *a1, (*a1).template custom_list_rect<T1>(f, f0));
      }
    }
  };

  template <typename A> struct rose {
    // TYPES
    struct Node {
      A a0;
      std::unique_ptr<custom_list<rose<A>>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Node _v) : v_(std::move(_v)) {}

    rose(const rose<A> &_other) : v_(std::move(_other.clone().v_)) {}

    rose(rose<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    rose<A> &operator=(const rose<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    rose<A> &operator=(rose<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    rose<A> clone() const {
      const auto &[a0, a1] = std::get<Node>(this->v());
      return rose<A>(Node{
          a0, a1 ? std::make_unique<NestedInd::custom_list<NestedInd::rose<A>>>(
                       a1->clone())
                 : nullptr});
    }

    // CREATORS
    template <typename _U> explicit rose(const rose<_U> &_other) {
      const auto &[a0, a1] = std::get<typename rose<_U>::Node>(_other.v());
      this->v_ = Node{
          A(a0), a1 ? std::make_unique<NestedInd::custom_list<rose<A>>>(*a1)
                    : nullptr};
    }

    static rose<A> node(A a0, custom_list<rose<A>> a1) {
      return rose(Node{std::move(a0),
                       std::make_unique<custom_list<rose<A>>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    unsigned int children_count() const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return (*a1).custom_list_length();
    }

    A root() const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return a0;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, custom_list<rose<A>> &>
    T1 rose_rec(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return f(a0, *a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, custom_list<rose<A>> &>
    T1 rose_rect(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose<A>::Node>(this->v());
      return f(a0, *a1);
    }
  };

  static rose<unsigned int> leaf(unsigned int n);
  static inline const rose<unsigned int> small_tree = rose<unsigned int>::node(
      1u,
      custom_list<rose<unsigned int>>::ccons(
          leaf(2u), custom_list<rose<unsigned int>>::ccons(
                        leaf(3u), custom_list<rose<unsigned int>>::cnil())));
  static inline const rose<unsigned int> bigger_tree = rose<unsigned int>::node(
      1u,
      custom_list<rose<unsigned int>>::ccons(
          small_tree, custom_list<rose<unsigned int>>::ccons(
                          leaf(4u), custom_list<rose<unsigned int>>::cnil())));
  static inline const unsigned int test_root_leaf = leaf(5u).root();
  static inline const unsigned int test_root_small = small_tree.root();
  static inline const unsigned int test_children_leaf =
      leaf(5u).children_count();
  static inline const unsigned int test_children_small =
      small_tree.children_count();
  static inline const unsigned int test_children_bigger =
      bigger_tree.children_count();

  struct expr {
    // TYPES
    struct Lit {
      unsigned int a0;
    };

    struct Add {
      std::unique_ptr<List<expr>> a0;
    };

    struct Mul {
      std::unique_ptr<List<expr>> a0;
    };

    using variant_t = std::variant<Lit, Add, Mul>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : v_(std::move(_v)) {}

    explicit expr(Add _v) : v_(std::move(_v)) {}

    explicit expr(Mul _v) : v_(std::move(_v)) {}

    expr(const expr &_other) : v_(std::move(_other.clone().v_)) {}

    expr(expr &&_other) noexcept : v_(std::move(_other.v_)) {}

    expr &operator=(const expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    expr &operator=(expr &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    expr clone() const {
      expr _out{};

      struct _CloneFrame {
        const expr *_src;
        expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const expr *_src = _frame._src;
        expr *_dst = _frame._dst;
        if (std::holds_alternative<Lit>(_src->v())) {
          const auto &_alt = std::get<Lit>(_src->v());
          _dst->v_ = Lit{_alt.a0};
        } else if (std::holds_alternative<Add>(_src->v())) {
          const auto &_alt = std::get<Add>(_src->v());
          _dst->v_ = Add{_alt.a0 ? std::make_unique<List<expr>>() : nullptr};
          auto &_dst_alt = std::get<Add>(_dst->v_);
          [&] {
            if (_alt.a0) {
              const List<expr> *_lsrc = _alt.a0.get();
              List<expr> *_ldst = _dst_alt.a0.get();
              while (std::holds_alternative<typename List<expr>::Cons>(
                  _lsrc->v())) {
                const auto &_lsrc_c =
                    std::get<typename List<expr>::Cons>(_lsrc->v());
                _ldst->v_mut() = typename List<expr>::Cons{
                    expr{},
                    _lsrc_c.a1 ? std::make_unique<List<expr>>() : nullptr};
                auto &_ldst_c =
                    std::get<typename List<expr>::Cons>(_ldst->v_mut());
                _stack.push_back({&_lsrc_c.a0, &_ldst_c.a0});
                if (_lsrc_c.a1) {
                  _lsrc = _lsrc_c.a1.get();
                  _ldst = _ldst_c.a1.get();
                } else {
                  break;
                }
              }
              if (std::holds_alternative<typename List<expr>::Nil>(
                      _lsrc->v())) {
                _ldst->v_mut() = typename List<expr>::Nil{};
              }
            }
          }();
        } else {
          const auto &_alt = std::get<Mul>(_src->v());
          _dst->v_ = Mul{_alt.a0 ? std::make_unique<List<expr>>() : nullptr};
          auto &_dst_alt = std::get<Mul>(_dst->v_);
          [&] {
            if (_alt.a0) {
              const List<expr> *_lsrc = _alt.a0.get();
              List<expr> *_ldst = _dst_alt.a0.get();
              while (std::holds_alternative<typename List<expr>::Cons>(
                  _lsrc->v())) {
                const auto &_lsrc_c =
                    std::get<typename List<expr>::Cons>(_lsrc->v());
                _ldst->v_mut() = typename List<expr>::Cons{
                    expr{},
                    _lsrc_c.a1 ? std::make_unique<List<expr>>() : nullptr};
                auto &_ldst_c =
                    std::get<typename List<expr>::Cons>(_ldst->v_mut());
                _stack.push_back({&_lsrc_c.a0, &_ldst_c.a0});
                if (_lsrc_c.a1) {
                  _lsrc = _lsrc_c.a1.get();
                  _ldst = _ldst_c.a1.get();
                } else {
                  break;
                }
              }
              if (std::holds_alternative<typename List<expr>::Nil>(
                      _lsrc->v())) {
                _ldst->v_mut() = typename List<expr>::Nil{};
              }
            }
          }();
        }
      }
      return _out;
    }

    // CREATORS
    static expr lit(unsigned int a0) { return expr(Lit{a0}); }

    static expr add(List<expr> a0) {
      return expr(Add{std::make_unique<List<expr>>(std::move(a0))});
    }

    static expr mul(List<expr> a0) {
      return expr(Mul{std::make_unique<List<expr>>(std::move(a0))});
    }

    // MANIPULATORS
    ~expr() {
      std::vector<std::unique_ptr<expr>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](expr &_node) {
        if (std::holds_alternative<Add>(_node.v_)) {
          auto &_alt = std::get<Add>(_node.v_);
          if (_alt.a0) {
            auto *_lp = _alt.a0.get();
            while (
                std::holds_alternative<typename List<expr>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<expr>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_unique<expr>(std::move(_lc.a0)));
              if (_lc.a1) {
                _lp = _lc.a1.get();
              } else {
                break;
              }
            }
          }
        }
        if (std::holds_alternative<Mul>(_node.v_)) {
          auto &_alt = std::get<Mul>(_node.v_);
          if (_alt.a0) {
            auto *_lp = _alt.a0.get();
            while (
                std::holds_alternative<typename List<expr>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<expr>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_unique<expr>(std::move(_lc.a0)));
              if (_lc.a1) {
                _lp = _lc.a1.get();
              } else {
                break;
              }
            }
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
    expr lit_map(F0 &&f) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return expr::lit(f(a0));
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return expr::add([&]() {
          auto aux_impl = [&](auto &_self_aux,
                              const List<expr> &l) -> List<expr> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<expr>::nil();
            } else {
              const auto &[a0, a1] = std::get<typename List<expr>::Cons>(l.v());
              return List<expr>::cons(a0.lit_map(f), _self_aux(_self_aux, *a1));
            }
          };
          auto aux = [&](const List<expr> &l) -> List<expr> {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }());
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return expr::mul([&]() {
          auto aux_impl = [&](auto &_self_aux,
                              const List<expr> &l) -> List<expr> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<expr>::nil();
            } else {
              const auto &[a0, a1] = std::get<typename List<expr>::Cons>(l.v());
              return List<expr>::cons(a0.lit_map(f), _self_aux(_self_aux, *a1));
            }
          };
          auto aux = [&](const List<expr> &l) -> List<expr> {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }());
      }
    }

    List<unsigned int> literals() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return List<unsigned int>::cons(a0, List<unsigned int>::nil());
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        auto aux_impl = [](auto &_self_aux,
                           const List<expr> &l) -> List<unsigned int> {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return List<unsigned int>::nil();
          } else {
            const auto &[a00, a10] = std::get<typename List<expr>::Cons>(l.v());
            return a00.literals().app(_self_aux(_self_aux, *a10));
          }
        };
        auto aux = [&](const List<expr> &l) -> List<unsigned int> {
          return aux_impl(aux_impl, l);
        };
        return aux(*a0);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        auto aux_impl = [](auto &_self_aux,
                           const List<expr> &l) -> List<unsigned int> {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return List<unsigned int>::nil();
          } else {
            const auto &[a00, a10] = std::get<typename List<expr>::Cons>(l.v());
            return a00.literals().app(_self_aux(_self_aux, *a10));
          }
        };
        auto aux = [&](const List<expr> &l) -> List<unsigned int> {
          return aux_impl(aux_impl, l);
        };
        return aux(*a0);
      }
    }

    unsigned int expr_depth() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        return 0u;
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return ([&]() {
          auto aux_impl = [](auto &_self_aux,
                             const List<expr> &l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[a0, a1] = std::get<typename List<expr>::Cons>(l.v());
              return std::max(a0.expr_depth(), _self_aux(_self_aux, *a1));
            }
          };
          auto aux = [&](const List<expr> &l) -> unsigned int {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }() + 1);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return ([&]() {
          auto aux_impl = [](auto &_self_aux,
                             const List<expr> &l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[a0, a1] = std::get<typename List<expr>::Cons>(l.v());
              return std::max(a0.expr_depth(), _self_aux(_self_aux, *a1));
            }
          };
          auto aux = [&](const List<expr> &l) -> unsigned int {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }() + 1);
      }
    }

    unsigned int expr_size() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        return 1u;
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return ([&]() {
          auto aux_impl = [](auto &_self_aux,
                             const List<expr> &l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[a0, a1] = std::get<typename List<expr>::Cons>(l.v());
              return (a0.expr_size() + _self_aux(_self_aux, *a1));
            }
          };
          auto aux = [&](const List<expr> &l) -> unsigned int {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }() + 1);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return ([&]() {
          auto aux_impl = [](auto &_self_aux,
                             const List<expr> &l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[a0, a1] = std::get<typename List<expr>::Cons>(l.v());
              return (a0.expr_size() + _self_aux(_self_aux, *a1));
            }
          };
          auto aux = [&](const List<expr> &l) -> unsigned int {
            return aux_impl(aux_impl, l);
          };
          return aux(*a0);
        }() + 1);
      }
    }

    unsigned int eval() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return a0;
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        auto sum_all_impl = [](auto &_self_sum_all,
                               const List<expr> &l) -> unsigned int {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return 0u;
          } else {
            const auto &[a00, a10] = std::get<typename List<expr>::Cons>(l.v());
            return (a00.eval() + _self_sum_all(_self_sum_all, *a10));
          }
        };
        auto sum_all = [&](const List<expr> &l) -> unsigned int {
          return sum_all_impl(sum_all_impl, l);
        };
        return sum_all(*a0);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        auto prod_all_impl = [](auto &_self_prod_all,
                                const List<expr> &l) -> unsigned int {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return 1u;
          } else {
            const auto &[a00, a10] = std::get<typename List<expr>::Cons>(l.v());
            return (a00.eval() * _self_prod_all(_self_prod_all, *a10));
          }
        };
        auto prod_all = [&](const List<expr> &l) -> unsigned int {
          return prod_all_impl(prod_all_impl, l);
        };
        return prod_all(*a0);
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, List<expr> &> &&
               std::is_invocable_r_v<T1, F2 &, List<expr> &>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return f0(*a0);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return f1(*a0);
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, List<expr> &> &&
               std::is_invocable_r_v<T1, F2 &, List<expr> &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0] = std::get<typename expr::Add>(this->v());
        return f0(*a0);
      } else {
        const auto &[a0] = std::get<typename expr::Mul>(this->v());
        return f1(*a0);
      }
    }
  };

  static inline const expr test_add = expr::add(List<expr>::cons(
      expr::lit(1u),
      List<expr>::cons(expr::lit(2u),
                       List<expr>::cons(expr::lit(3u), List<expr>::nil()))));
  static inline const expr test_mul = expr::mul(List<expr>::cons(
      expr::lit(2u),
      List<expr>::cons(expr::lit(3u),
                       List<expr>::cons(expr::lit(4u), List<expr>::nil()))));
  static inline const expr test_nested = expr::mul(List<expr>::cons(
      expr::add(List<expr>::cons(
          expr::lit(1u), List<expr>::cons(expr::lit(2u), List<expr>::nil()))),
      List<expr>::cons(expr::add(List<expr>::cons(
                           expr::lit(3u),
                           List<expr>::cons(expr::lit(4u), List<expr>::nil()))),
                       List<expr>::nil())));
  static inline const unsigned int test_eval_add = test_add.eval();
  static inline const unsigned int test_eval_mul = test_mul.eval();
  static inline const unsigned int test_eval_nested = test_nested.eval();
  static inline const unsigned int test_size_nested = test_nested.expr_size();
  static inline const unsigned int test_depth_nested = test_nested.expr_depth();
  static inline const List<unsigned int> test_literals = test_nested.literals();
  static inline const unsigned int test_doubled =
      test_nested.lit_map([](unsigned int n) { return (n * 2u); }).eval();
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<
                              std::pair<
                                  std::pair<std::pair<std::pair<unsigned int,
                                                                unsigned int>,
                                                      unsigned int>,
                                            unsigned int>,
                                  unsigned int>,
                              unsigned int>,
                          unsigned int>,
                      unsigned int>,
                  unsigned int>,
              unsigned int>,
          List<unsigned int>>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(
                              std::make_pair(
                                  std::make_pair(
                                      std::make_pair(
                                          std::make_pair(
                                              std::make_pair(test_root_leaf,
                                                             test_root_small),
                                              test_children_leaf),
                                          test_children_small),
                                      test_children_bigger),
                                  test_eval_add),
                              test_eval_mul),
                          test_eval_nested),
                      test_size_nested),
                  test_depth_nested),
              test_literals),
          test_doubled);
};

#endif // INCLUDED_NESTED_IND
