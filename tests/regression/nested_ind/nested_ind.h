#ifndef INCLUDED_NESTED_IND
#define INCLUDED_NESTED_IND

#include <algorithm>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
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

  List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(std::move(m)));
    }
  }
};

struct NestedInd {
  template <typename t_A> struct custom_list {
    // TYPES
    struct Cnil {};

    struct Ccons {
      t_A d_a0;
      std::unique_ptr<custom_list<t_A>> d_a1;
    };

    using variant_t = std::variant<Cnil, Ccons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    custom_list() {}

    explicit custom_list(Cnil _v) : d_v_(_v) {}

    explicit custom_list(Ccons _v) : d_v_(std::move(_v)) {}

    custom_list(const custom_list<t_A> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    custom_list(custom_list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    custom_list<t_A> &operator=(const custom_list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    custom_list<t_A> &operator=(custom_list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    custom_list clone() const {
      custom_list _out{};

      struct _CloneFrame {
        const custom_list *_src;
        custom_list *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const custom_list *_src = _frame._src;
        custom_list *_dst = _frame._dst;
        if (std::holds_alternative<Cnil>(_src->v())) {
          const auto &_alt = std::get<Cnil>(_src->v());
          _dst->d_v_ = Cnil{};
        } else {
          const auto &_alt = std::get<Ccons>(_src->v());
          _dst->d_v_ = Ccons{
              _alt.d_a0, _alt.d_a1 ? std::make_unique<custom_list>() : nullptr};
          auto &_dst_alt = std::get<Ccons>(_dst->d_v_);
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit custom_list(const custom_list<_U> &_other) {
      if (std::holds_alternative<typename custom_list<_U>::Cnil>(_other.v())) {
        d_v_ = Cnil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename custom_list<_U>::Ccons>(_other.v());
        d_v_ = Ccons{t_A(d_a0), d_a1 ? std::make_unique<custom_list<t_A>>(*d_a1)
                                     : nullptr};
      }
    }

    static custom_list<t_A> cnil() { return custom_list(Cnil{}); }

    static custom_list<t_A> ccons(t_A a0, custom_list<t_A> a1) {
      return custom_list(Ccons{
          std::move(a0), std::make_unique<custom_list<t_A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~custom_list() {
      std::vector<std::unique_ptr<custom_list>> _stack;
      auto _drain = [&](custom_list &_node) {
        if (std::holds_alternative<Ccons>(_node.d_v_)) {
          auto &_alt = std::get<Ccons>(_node.d_v_);
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

    unsigned int custom_list_length() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename custom_list<t_A>::Cnil>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename custom_list<t_A>::Ccons>(_sv.v());
        return (1u + (*(d_a1)).custom_list_length());
      }
    }

    template <typename T1, MapsTo<T1, t_A, custom_list<t_A>, T1> F1>
    T1 custom_list_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename custom_list<t_A>::Cnil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename custom_list<t_A>::Ccons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template custom_list_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, t_A, custom_list<t_A>, T1> F1>
    T1 custom_list_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename custom_list<t_A>::Cnil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename custom_list<t_A>::Ccons>(_sv.v());
        return f0(d_a0, *(d_a1),
                  (*(d_a1)).template custom_list_rect<T1>(f, f0));
      }
    }
  };

  template <typename t_A> struct rose {
    // TYPES
    struct Node {
      t_A d_a0;
      std::unique_ptr<custom_list<rose<t_A>>> d_a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Node _v) : d_v_(std::move(_v)) {}

    rose(const rose<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    rose(rose<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    rose<t_A> &operator=(const rose<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    rose<t_A> &operator=(rose<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    rose<t_A> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Node>(_sv.v());
      return rose<t_A>(Node{
          d_a0,
          d_a1 ? std::make_unique<NestedInd::custom_list<NestedInd::rose<t_A>>>(
                     d_a1->clone())
               : nullptr});
    }

    // CREATORS
    template <typename _U> explicit rose(const rose<_U> &_other) {
      const auto &[d_a0, d_a1] = std::get<typename rose<_U>::Node>(_other.v());
      d_v_ =
          Node{t_A(d_a0),
               d_a1 ? std::make_unique<NestedInd::custom_list<rose<t_A>>>(*d_a1)
                    : nullptr};
    }

    static rose<t_A> node(t_A a0, custom_list<rose<t_A>> a1) {
      return rose(Node{std::move(a0), std::make_unique<custom_list<rose<t_A>>>(
                                          std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int children_count() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(_sv.v());
      return (*(d_a1)).custom_list_length();
    }

    t_A root() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(_sv.v());
      return d_a0;
    }

    template <typename T1, MapsTo<T1, t_A, custom_list<rose<t_A>>> F0>
    T1 rose_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(_sv.v());
      return f(d_a0, *(d_a1));
    }

    template <typename T1, MapsTo<T1, t_A, custom_list<rose<t_A>>> F0>
    T1 rose_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(_sv.v());
      return f(d_a0, *(d_a1));
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
      unsigned int d_a0;
    };

    struct Add {
      std::unique_ptr<List<expr>> d_a0;
    };

    struct Mul {
      std::unique_ptr<List<expr>> d_a0;
    };

    using variant_t = std::variant<Lit, Add, Mul>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit expr(Add _v) : d_v_(std::move(_v)) {}

    explicit expr(Mul _v) : d_v_(std::move(_v)) {}

    expr(const expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    expr(expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    expr &operator=(const expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    expr &operator=(expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    expr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<Lit>(_sv.v());
        return expr(Lit{d_a0});
      } else if (std::holds_alternative<Add>(_sv.v())) {
        const auto &[d_a0] = std::get<Add>(_sv.v());
        return expr(
            Add{d_a0 ? std::make_unique<List<NestedInd::expr>>(d_a0->clone())
                     : nullptr});
      } else {
        const auto &[d_a0] = std::get<Mul>(_sv.v());
        return expr(
            Mul{d_a0 ? std::make_unique<List<NestedInd::expr>>(d_a0->clone())
                     : nullptr});
      }
    }

    // CREATORS
    static expr lit(unsigned int a0) { return expr(Lit{std::move(a0)}); }

    static expr add(List<expr> a0) {
      return expr(Add{std::make_unique<List<expr>>(std::move(a0))});
    }

    static expr mul(List<expr> a0) {
      return expr(Mul{std::make_unique<List<expr>>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    template <MapsTo<unsigned int, unsigned int> F0>
    expr lit_map(F0 &&f) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
        return expr::lit(f(d_a0));
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        List<expr> d_a0_value = List<NestedInd::expr>(*(d_a0));
        return expr::add([&]() {
          std::function<List<expr>(List<expr>)> aux;
          aux = [&](List<expr> l) -> List<expr> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<expr>::nil();
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return List<expr>::cons(d_a0.lit_map(f), aux(*(d_a1)));
            }
          };
          return aux(d_a0_value);
        }());
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        List<expr> d_a0_value = List<NestedInd::expr>(*(d_a0));
        return expr::mul([&]() {
          std::function<List<expr>(List<expr>)> aux;
          aux = [&](List<expr> l) -> List<expr> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<expr>::nil();
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return List<expr>::cons(d_a0.lit_map(f), aux(*(d_a1)));
            }
          };
          return aux(d_a0_value);
        }());
      }
    }

    List<unsigned int> literals() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
        return List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        List<expr> d_a0_value = List<NestedInd::expr>(*(d_a0));
        std::function<List<unsigned int>(List<expr>)> aux;
        aux = [&](List<expr> l) -> List<unsigned int> {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return List<unsigned int>::nil();
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<expr>::Cons>(l.v());
            return d_a00.literals().app(aux(*(d_a10)));
          }
        };
        return aux(d_a0_value);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        List<expr> d_a0_value = List<NestedInd::expr>(*(d_a0));
        std::function<List<unsigned int>(List<expr>)> aux;
        aux = [&](List<expr> l) -> List<unsigned int> {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return List<unsigned int>::nil();
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<expr>::Cons>(l.v());
            return d_a00.literals().app(aux(*(d_a10)));
          }
        };
        return aux(d_a0_value);
      }
    }

    unsigned int expr_depth() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        return 0u;
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        List<expr> d_a0_value = List<NestedInd::expr>(*(d_a0));
        return ([&]() {
          std::function<unsigned int(List<expr>)> aux;
          aux = [&](List<expr> l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return std::max(d_a0.expr_depth(), aux(*(d_a1)));
            }
          };
          return aux(d_a0_value);
        }() + 1);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        List<expr> d_a0_value = List<NestedInd::expr>(*(d_a0));
        return ([&]() {
          std::function<unsigned int(List<expr>)> aux;
          aux = [&](List<expr> l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return std::max(d_a0.expr_depth(), aux(*(d_a1)));
            }
          };
          return aux(d_a0_value);
        }() + 1);
      }
    }

    unsigned int expr_size() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        return 1u;
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        List<expr> d_a0_value = List<NestedInd::expr>(*(d_a0));
        return ([&]() {
          std::function<unsigned int(List<expr>)> aux;
          aux = [&](List<expr> l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return (d_a0.expr_size() + aux(*(d_a1)));
            }
          };
          return aux(d_a0_value);
        }() + 1);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        List<expr> d_a0_value = List<NestedInd::expr>(*(d_a0));
        return ([&]() {
          std::function<unsigned int(List<expr>)> aux;
          aux = [&](List<expr> l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return (d_a0.expr_size() + aux(*(d_a1)));
            }
          };
          return aux(d_a0_value);
        }() + 1);
      }
    }

    unsigned int eval() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        List<expr> d_a0_value = List<NestedInd::expr>(*(d_a0));
        std::function<unsigned int(List<expr>)> sum_all;
        sum_all = [&](List<expr> l) -> unsigned int {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return 0u;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<expr>::Cons>(l.v());
            return (d_a00.eval() + sum_all(*(d_a10)));
          }
        };
        return sum_all(d_a0_value);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        List<expr> d_a0_value = List<NestedInd::expr>(*(d_a0));
        std::function<unsigned int(List<expr>)> prod_all;
        prod_all = [&](List<expr> l) -> unsigned int {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return 1u;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<expr>::Cons>(l.v());
            return (d_a00.eval() * prod_all(*(d_a10)));
          }
        };
        return prod_all(d_a0_value);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, List<expr>> F1, MapsTo<T1, List<expr>> F2>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        return f0(*(d_a0));
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        return f1(*(d_a0));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, List<expr>> F1, MapsTo<T1, List<expr>> F2>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        return f0(*(d_a0));
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        return f1(*(d_a0));
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
      test_nested.lit_map([](const unsigned int &n) { return (n * 2u); })
          .eval();
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
