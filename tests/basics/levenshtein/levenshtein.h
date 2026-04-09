#ifndef INCLUDED_LEVENSHTEIN
#define INCLUDED_LEVENSHTEIN

#include <functional>
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

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Nat(O _v) : d_v_(std::move(_v)) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Nat> o() { return std::make_shared<Nat>(O{}); }

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &a0) {
    return std::make_shared<Nat>(S{a0});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&a0) {
    return std::make_shared<Nat>(S{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) Bool0 leb(const std::shared_ptr<Nat> &m) const {
    return std::visit(
        Overloaded{
            [](const typename Nat::O _args) -> Bool0 { return Bool0::e_TRUE0; },
            [&](const typename Nat::S _args) -> Bool0 {
              return std::visit(
                  Overloaded{[](const typename Nat::O _args0) -> Bool0 {
                               return Bool0::e_FALSE0;
                             },
                             [&](const typename Nat::S _args0) -> Bool0 {
                               return _args.d_a0->leb(_args0.d_a0);
                             }},
                  m->v());
            }},
        this->v());
  }
};

template <typename t_A, typename t_P> struct SigT {
  // TYPES
  struct ExistT {
    t_A d_x;
    t_P d_a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit SigT(ExistT _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<SigT<t_A, t_P>> existt(t_A x, t_P a1) {
    return std::make_shared<SigT<t_A, t_P>>(
        ExistT{std::move(x), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A projT1() const {
    return std::visit(
        Overloaded{[](const typename SigT<t_A, t_P>::ExistT _args) -> t_A {
          return _args.d_x;
        }},
        this->v());
  }
};
enum class Sumbool { e_LEFT, e_RIGHT };

struct Bool {
  __attribute__((pure)) static Sumbool bool_dec(const Bool0 b1, const Bool0 b2);
};

struct Ascii {
  // TYPES
  struct Ascii0 {
    Bool0 d_a0;
    Bool0 d_a1;
    Bool0 d_a2;
    Bool0 d_a3;
    Bool0 d_a4;
    Bool0 d_a5;
    Bool0 d_a6;
    Bool0 d_a7;
  };

  using variant_t = std::variant<Ascii0>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Ascii(Ascii0 _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Ascii> ascii0(Bool0 a0, Bool0 a1, Bool0 a2, Bool0 a3,
                                       Bool0 a4, Bool0 a5, Bool0 a6, Bool0 a7) {
    return std::make_shared<Ascii>(
        Ascii0{std::move(a0), std::move(a1), std::move(a2), std::move(a3),
               std::move(a4), std::move(a5), std::move(a6), std::move(a7)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) Sumbool
  ascii_dec(const std::shared_ptr<Ascii> &b) const {
    return std::visit(
        Overloaded{[&](const typename Ascii::Ascii0 _args) -> auto {
          return std::visit(
              Overloaded{[&](const typename Ascii::Ascii0 _args0) -> Sumbool {
                switch (Bool::bool_dec(_args.d_a0, _args0.d_a0)) {
                case Sumbool::e_LEFT: {
                  switch (Bool::bool_dec(_args.d_a1, _args0.d_a1)) {
                  case Sumbool::e_LEFT: {
                    switch (Bool::bool_dec(_args.d_a2, _args0.d_a2)) {
                    case Sumbool::e_LEFT: {
                      switch (Bool::bool_dec(_args.d_a3, _args0.d_a3)) {
                      case Sumbool::e_LEFT: {
                        switch (Bool::bool_dec(_args.d_a4, _args0.d_a4)) {
                        case Sumbool::e_LEFT: {
                          switch (Bool::bool_dec(_args.d_a5, _args0.d_a5)) {
                          case Sumbool::e_LEFT: {
                            switch (Bool::bool_dec(_args.d_a6, _args0.d_a6)) {
                            case Sumbool::e_LEFT: {
                              switch (Bool::bool_dec(_args.d_a7, _args0.d_a7)) {
                              case Sumbool::e_LEFT: {
                                return Sumbool::e_LEFT;
                              }
                              case Sumbool::e_RIGHT: {
                                return Sumbool::e_RIGHT;
                              }
                              default:
                                std::unreachable();
                              }
                            }
                            case Sumbool::e_RIGHT: {
                              return Sumbool::e_RIGHT;
                            }
                            default:
                              std::unreachable();
                            }
                          }
                          case Sumbool::e_RIGHT: {
                            return Sumbool::e_RIGHT;
                          }
                          default:
                            std::unreachable();
                          }
                        }
                        case Sumbool::e_RIGHT: {
                          return Sumbool::e_RIGHT;
                        }
                        default:
                          std::unreachable();
                        }
                      }
                      case Sumbool::e_RIGHT: {
                        return Sumbool::e_RIGHT;
                      }
                      default:
                        std::unreachable();
                      }
                    }
                    case Sumbool::e_RIGHT: {
                      return Sumbool::e_RIGHT;
                    }
                    default:
                      std::unreachable();
                    }
                  }
                  case Sumbool::e_RIGHT: {
                    return Sumbool::e_RIGHT;
                  }
                  default:
                    std::unreachable();
                  }
                }
                case Sumbool::e_RIGHT: {
                  return Sumbool::e_RIGHT;
                }
                default:
                  std::unreachable();
                }
              }},
              b->v());
        }},
        this->v());
  }
};

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    std::shared_ptr<Ascii> d_a0;
    std::shared_ptr<String> d_a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit String(EmptyString _v) : d_v_(std::move(_v)) {}

  explicit String(String0 _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<String> emptystring() {
    return std::make_shared<String>(EmptyString{});
  }

  static std::shared_ptr<String> string0(const std::shared_ptr<Ascii> &a0,
                                         const std::shared_ptr<String> &a1) {
    return std::make_shared<String>(String0{a0, a1});
  }

  static std::shared_ptr<String> string0(std::shared_ptr<Ascii> &&a0,
                                         std::shared_ptr<String> &&a1) {
    return std::make_shared<String>(String0{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<String> append(std::shared_ptr<String> s2) const {
    return std::visit(Overloaded{[&](const typename String::EmptyString _args)
                                     -> std::shared_ptr<String> { return s2; },
                                 [&](const typename String::String0 _args)
                                     -> std::shared_ptr<String> {
                                   return String::string0(
                                       _args.d_a0, _args.d_a1->append(s2));
                                 }},
                      this->v());
  }

  std::shared_ptr<Nat> length() const {
    return std::visit(
        Overloaded{
            [](const typename String::EmptyString _args)
                -> std::shared_ptr<Nat> { return Nat::o(); },
            [](const typename String::String0 _args) -> std::shared_ptr<Nat> {
              return Nat::s(_args.d_a1->length());
            }},
        this->v());
  }
};

struct Levenshtein {
  struct edit {
    // TYPES
    struct Insertion {
      std::shared_ptr<Ascii> d_a;
      std::shared_ptr<String> d_s;
    };

    struct Deletion {
      std::shared_ptr<Ascii> d_a;
      std::shared_ptr<String> d_s;
    };

    struct Update {
      std::shared_ptr<Ascii> d_a;
      std::shared_ptr<Ascii> d_a_1;
      std::shared_ptr<String> d_neq;
    };

    using variant_t = std::variant<Insertion, Deletion, Update>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit edit(Insertion _v) : d_v_(std::move(_v)) {}

    explicit edit(Deletion _v) : d_v_(std::move(_v)) {}

    explicit edit(Update _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<edit> insertion(const std::shared_ptr<Ascii> &a,
                                           const std::shared_ptr<String> &s) {
      return std::make_shared<edit>(Insertion{a, s});
    }

    static std::shared_ptr<edit> insertion(std::shared_ptr<Ascii> &&a,
                                           std::shared_ptr<String> &&s) {
      return std::make_shared<edit>(Insertion{std::move(a), std::move(s)});
    }

    static std::shared_ptr<edit> deletion(const std::shared_ptr<Ascii> &a,
                                          const std::shared_ptr<String> &s) {
      return std::make_shared<edit>(Deletion{a, s});
    }

    static std::shared_ptr<edit> deletion(std::shared_ptr<Ascii> &&a,
                                          std::shared_ptr<String> &&s) {
      return std::make_shared<edit>(Deletion{std::move(a), std::move(s)});
    }

    static std::shared_ptr<edit> update(const std::shared_ptr<Ascii> &a,
                                        const std::shared_ptr<Ascii> &a_1,
                                        const std::shared_ptr<String> &neq) {
      return std::make_shared<edit>(Update{a, a_1, neq});
    }

    static std::shared_ptr<edit> update(std::shared_ptr<Ascii> &&a,
                                        std::shared_ptr<Ascii> &&a_1,
                                        std::shared_ptr<String> &&neq) {
      return std::make_shared<edit>(
          Update{std::move(a), std::move(a_1), std::move(neq)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1,
              MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<String>> F0,
              MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<String>> F1,
              MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<Ascii>,
                     std::shared_ptr<String>>
                  F2>
    T1 edit_rec(F0 &&f, F1 &&f0, F2 &&f1, const std::shared_ptr<String> &_x,
                const std::shared_ptr<String> &_x0) const {
      return std::visit(
          Overloaded{[&](const typename edit::Insertion _args) -> T1 {
                       return f(_args.d_a, _args.d_s);
                     },
                     [&](const typename edit::Deletion _args) -> T1 {
                       return f0(_args.d_a, _args.d_s);
                     },
                     [&](const typename edit::Update _args) -> T1 {
                       return f1(_args.d_a, _args.d_a_1, _args.d_neq);
                     }},
          this->v());
    }

    template <typename T1,
              MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<String>> F0,
              MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<String>> F1,
              MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<Ascii>,
                     std::shared_ptr<String>>
                  F2>
    T1 edit_rect(F0 &&f, F1 &&f0, F2 &&f1, const std::shared_ptr<String> &_x,
                 const std::shared_ptr<String> &_x0) const {
      return std::visit(
          Overloaded{[&](const typename edit::Insertion _args) -> T1 {
                       return f(_args.d_a, _args.d_s);
                     },
                     [&](const typename edit::Deletion _args) -> T1 {
                       return f0(_args.d_a, _args.d_s);
                     },
                     [&](const typename edit::Update _args) -> T1 {
                       return f1(_args.d_a, _args.d_a_1, _args.d_neq);
                     }},
          this->v());
    }
  };

  struct chain : public std::enable_shared_from_this<chain> {
    // TYPES
    struct Empty {};

    struct Skip {
      std::shared_ptr<Ascii> d_a;
      std::shared_ptr<String> d_s;
      std::shared_ptr<String> d_t;
      std::shared_ptr<Nat> d_n;
      std::shared_ptr<chain> d_a4;
    };

    struct Change {
      std::shared_ptr<String> d_s;
      std::shared_ptr<String> d_t;
      std::shared_ptr<String> d_u;
      std::shared_ptr<Nat> d_n;
      std::shared_ptr<edit> d_a4;
      std::shared_ptr<chain> d_a5;
    };

    using variant_t = std::variant<Empty, Skip, Change>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit chain(Empty _v) : d_v_(std::move(_v)) {}

    explicit chain(Skip _v) : d_v_(std::move(_v)) {}

    explicit chain(Change _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<chain> empty() {
      return std::make_shared<chain>(Empty{});
    }

    static std::shared_ptr<chain> skip(const std::shared_ptr<Ascii> &a,
                                       const std::shared_ptr<String> &s,
                                       const std::shared_ptr<String> &t,
                                       const std::shared_ptr<Nat> &n,
                                       const std::shared_ptr<chain> &a4) {
      return std::make_shared<chain>(Skip{a, s, t, n, a4});
    }

    static std::shared_ptr<chain> skip(std::shared_ptr<Ascii> &&a,
                                       std::shared_ptr<String> &&s,
                                       std::shared_ptr<String> &&t,
                                       std::shared_ptr<Nat> &&n,
                                       std::shared_ptr<chain> &&a4) {
      return std::make_shared<chain>(Skip{std::move(a), std::move(s),
                                          std::move(t), std::move(n),
                                          std::move(a4)});
    }

    static std::shared_ptr<chain>
    change(const std::shared_ptr<String> &s, const std::shared_ptr<String> &t,
           const std::shared_ptr<String> &u, const std::shared_ptr<Nat> &n,
           const std::shared_ptr<edit> &a4, const std::shared_ptr<chain> &a5) {
      return std::make_shared<chain>(Change{s, t, u, n, a4, a5});
    }

    static std::shared_ptr<chain>
    change(std::shared_ptr<String> &&s, std::shared_ptr<String> &&t,
           std::shared_ptr<String> &&u, std::shared_ptr<Nat> &&n,
           std::shared_ptr<edit> &&a4, std::shared_ptr<chain> &&a5) {
      return std::make_shared<chain>(Change{std::move(s), std::move(t),
                                            std::move(u), std::move(n),
                                            std::move(a4), std::move(a5)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    std::shared_ptr<chain> aux_eq_char(const std::shared_ptr<String> &_x,
                                       const std::shared_ptr<String> &_x0,
                                       const std::shared_ptr<Ascii> &_x1,
                                       std::shared_ptr<String> xs,
                                       std::shared_ptr<Ascii> y,
                                       std::shared_ptr<String> ys,
                                       std::shared_ptr<Nat> n) const {
      return chain::skip(
          y, xs, ys, n,
          std::const_pointer_cast<chain>(this->shared_from_this()));
    }

    std::shared_ptr<chain> aux_update(const std::shared_ptr<String> &_x,
                                      const std::shared_ptr<String> &_x0,
                                      const std::shared_ptr<Ascii> &x,
                                      const std::shared_ptr<String> &xs,
                                      const std::shared_ptr<Ascii> &y,
                                      const std::shared_ptr<String> &ys,
                                      const std::shared_ptr<Nat> &n) const {
      return std::const_pointer_cast<chain>(this->shared_from_this())
          ->update_chain(x, y, xs, ys, n);
    }

    std::shared_ptr<chain> aux_delete(const std::shared_ptr<String> &_x,
                                      const std::shared_ptr<String> &_x0,
                                      const std::shared_ptr<Ascii> &x,
                                      const std::shared_ptr<String> &xs,
                                      std::shared_ptr<Ascii> y,
                                      std::shared_ptr<String> ys,
                                      const std::shared_ptr<Nat> &n) const {
      return std::const_pointer_cast<chain>(this->shared_from_this())
          ->delete_chain(x, xs, String::string0(y, ys), n);
    }

    std::shared_ptr<chain> aux_insert(const std::shared_ptr<String> &_x,
                                      const std::shared_ptr<String> &_x0,
                                      std::shared_ptr<Ascii> x,
                                      std::shared_ptr<String> xs,
                                      const std::shared_ptr<Ascii> &y,
                                      const std::shared_ptr<String> &ys,
                                      const std::shared_ptr<Nat> &n) const {
      return std::const_pointer_cast<chain>(this->shared_from_this())
          ->insert_chain(y, String::string0(x, xs), ys, n);
    }

    std::shared_ptr<chain> update_chain(std::shared_ptr<Ascii> c,
                                        std::shared_ptr<Ascii> c_,
                                        std::shared_ptr<String> s1,
                                        std::shared_ptr<String> s2,
                                        std::shared_ptr<Nat> n) const {
      return chain::change(String::string0(c, s1), String::string0(c_, s1),
                           String::string0(c_, s2), n, edit::update(c, c_, s1),
                           chain::skip(c_, s1, s2, n,
                                       std::const_pointer_cast<chain>(
                                           this->shared_from_this())));
    }

    std::shared_ptr<chain> delete_chain(std::shared_ptr<Ascii> c,
                                        std::shared_ptr<String> s1,
                                        std::shared_ptr<String> s2,
                                        std::shared_ptr<Nat> n) const {
      return chain::change(
          String::string0(c, s1), s1, s2, n, edit::deletion(c, s1),
          std::const_pointer_cast<chain>(this->shared_from_this()));
    }

    std::shared_ptr<chain> insert_chain(std::shared_ptr<Ascii> c,
                                        std::shared_ptr<String> s1,
                                        std::shared_ptr<String> s2,
                                        std::shared_ptr<Nat> n) const {
      return chain::change(s1, String::string0(c, s1), String::string0(c, s2),
                           n, edit::insertion(c, s1),
                           chain::skip(c, s1, s2, n,
                                       std::const_pointer_cast<chain>(
                                           this->shared_from_this())));
    }
  };

  template <typename T1,
            MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<String>,
                   std::shared_ptr<String>, std::shared_ptr<Nat>,
                   std::shared_ptr<chain>, T1>
                F1,
            MapsTo<T1, std::shared_ptr<String>, std::shared_ptr<String>,
                   std::shared_ptr<String>, std::shared_ptr<Nat>,
                   std::shared_ptr<edit>, std::shared_ptr<chain>, T1>
                F2>
  static T1
  chain_rect(const T1 f, F1 &&f0, F2 &&f1, const std::shared_ptr<String> &_x,
             const std::shared_ptr<String> &_x0,
             const std::shared_ptr<Nat> &_x1, const std::shared_ptr<chain> &c) {
    return std::visit(
        Overloaded{[&](const typename chain::Empty _args) -> T1 { return f; },
                   [&](const typename chain::Skip _args) -> T1 {
                     return f0(_args.d_a, _args.d_s, _args.d_t, _args.d_n,
                               _args.d_a4,
                               chain_rect<T1>(f, f0, f1, _args.d_s, _args.d_t,
                                              _args.d_n, _args.d_a4));
                   },
                   [&](const typename chain::Change _args) -> T1 {
                     return f1(_args.d_s, _args.d_t, _args.d_u, _args.d_n,
                               _args.d_a4, _args.d_a5,
                               chain_rect<T1>(f, f0, f1, _args.d_t, _args.d_u,
                                              _args.d_n, _args.d_a5));
                   }},
        c->v());
  }

  template <typename T1,
            MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<String>,
                   std::shared_ptr<String>, std::shared_ptr<Nat>,
                   std::shared_ptr<chain>, T1>
                F1,
            MapsTo<T1, std::shared_ptr<String>, std::shared_ptr<String>,
                   std::shared_ptr<String>, std::shared_ptr<Nat>,
                   std::shared_ptr<edit>, std::shared_ptr<chain>, T1>
                F2>
  static T1
  chain_rec(const T1 f, F1 &&f0, F2 &&f1, const std::shared_ptr<String> &_x,
            const std::shared_ptr<String> &_x0, const std::shared_ptr<Nat> &_x1,
            const std::shared_ptr<chain> &c) {
    return std::visit(
        Overloaded{[&](const typename chain::Empty _args) -> T1 { return f; },
                   [&](const typename chain::Skip _args) -> T1 {
                     return f0(_args.d_a, _args.d_s, _args.d_t, _args.d_n,
                               _args.d_a4,
                               chain_rec<T1>(f, f0, f1, _args.d_s, _args.d_t,
                                             _args.d_n, _args.d_a4));
                   },
                   [&](const typename chain::Change _args) -> T1 {
                     return f1(_args.d_s, _args.d_t, _args.d_u, _args.d_n,
                               _args.d_a4, _args.d_a5,
                               chain_rec<T1>(f, f0, f1, _args.d_t, _args.d_u,
                                             _args.d_n, _args.d_a5));
                   }},
        c->v());
  }

  static std::shared_ptr<chain> same_chain(const std::shared_ptr<String> &s);

  template <typename T1>
  static T1 _inserts_chain_F(const std::shared_ptr<String> &s) {
    return std::visit(
        Overloaded{[](const typename String::EmptyString _args0) -> T1 {
                     return chain::empty();
                   },
                   [](const typename String::String0 _args0) -> T1 {
                     return chain::skip(_args0.d_a0, _args0.d_a1, _args0.d_a1,
                                        Nat::o(),
                                        _inserts_chain_F<T1>(_args0.d_a1));
                   }},
        s->v());
  }

  static std::shared_ptr<chain>
  inserts_chain(const std::shared_ptr<String> &s1,
                const std::shared_ptr<String> &s2);
  static std::shared_ptr<chain>
  inserts_chain_empty(const std::shared_ptr<String> &s);
  static std::shared_ptr<chain>
  deletes_chain(const std::shared_ptr<String> &s1,
                const std::shared_ptr<String> &s2);
  static std::shared_ptr<chain>
  deletes_chain_empty(const std::shared_ptr<String> &s);
  static std::shared_ptr<chain>
  aux_both_empty(const std::shared_ptr<String> &_x,
                 const std::shared_ptr<String> &_x0);

  template <typename T1, MapsTo<std::shared_ptr<Nat>, T1> F3>
  static T1 min3_app(const T1 x, const T1 y, const T1 z, F3 &&f) {
    std::shared_ptr<Nat> n1 = f(x);
    std::shared_ptr<Nat> n2 = f(y);
    std::shared_ptr<Nat> n3 = f(z);
    switch (n1->leb(n2)) {
    case Bool0::e_TRUE0: {
      switch (std::move(n1)->leb(std::move(n3))) {
      case Bool0::e_TRUE0: {
        return x;
      }
      case Bool0::e_FALSE0: {
        return z;
      }
      default:
        std::unreachable();
      }
    }
    case Bool0::e_FALSE0: {
      switch (std::move(n2)->leb(std::move(n3))) {
      case Bool0::e_TRUE0: {
        return y;
      }
      case Bool0::e_FALSE0: {
        return z;
      }
      default:
        std::unreachable();
      }
    }
    default:
      std::unreachable();
    }
  }

  static std::shared_ptr<SigT<std::shared_ptr<Nat>, std::shared_ptr<chain>>>
  levenshtein_chain(const std::shared_ptr<String> &s,
                    std::shared_ptr<String> _x0);
  static std::shared_ptr<Nat>
  levenshtein_computed(const std::shared_ptr<String> &s,
                       const std::shared_ptr<String> &t);
  static std::shared_ptr<Nat> levenshtein(const std::shared_ptr<String> &_x0,
                                          const std::shared_ptr<String> &_x1);
};

#endif // INCLUDED_LEVENSHTEIN
