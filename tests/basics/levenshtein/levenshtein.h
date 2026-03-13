#ifndef INCLUDED_LEVENSHTEIN
#define INCLUDED_LEVENSHTEIN

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

  // CREATORS
  explicit Nat(O _v) : d_v_(std::move(_v)) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Nat> O_() {
      return std::shared_ptr<Nat>(new Nat(O{}));
    }

    static std::shared_ptr<Nat> S_(const std::shared_ptr<Nat> &a0) {
      return std::shared_ptr<Nat>(new Nat(S{a0}));
    }

    static std::unique_ptr<Nat> O_uptr() {
      return std::unique_ptr<Nat>(new Nat(O{}));
    }

    static std::unique_ptr<Nat> S_uptr(const std::shared_ptr<Nat> &a0) {
      return std::unique_ptr<Nat>(new Nat(S{a0}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) Bool0 leb(const std::shared_ptr<Nat> &m) const {
    return std::visit(
        Overloaded{
            [](const typename Nat::O _args) -> Bool0 { return Bool0::e_TRUE0; },
            [&](const typename Nat::S _args) -> Bool0 {
              std::shared_ptr<Nat> n_ = _args.d_a0;
              return std::visit(
                  Overloaded{[](const typename Nat::O _args) -> Bool0 {
                               return Bool0::e_FALSE0;
                             },
                             [&](const typename Nat::S _args) -> Bool0 {
                               std::shared_ptr<Nat> m_ = _args.d_a0;
                               return std::move(n_)->leb(std::move(m_));
                             }},
                  m->v());
            }},
        this->v());
  }
};

template <typename t_A, typename t_P> struct SigT {
  // TYPES
  struct ExistT {
    t_A d_a0;
    t_P d_a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit SigT(ExistT _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<SigT<t_A, t_P>> ExistT_(t_A a0, t_P a1) {
      return std::shared_ptr<SigT<t_A, t_P>>(
          new SigT<t_A, t_P>(ExistT{a0, a1}));
    }

    static std::unique_ptr<SigT<t_A, t_P>> ExistT_uptr(t_A a0, t_P a1) {
      return std::unique_ptr<SigT<t_A, t_P>>(
          new SigT<t_A, t_P>(ExistT{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A projT1() const {
    return std::visit(
        Overloaded{[](const typename SigT<t_A, t_P>::ExistT _args) -> t_A {
          t_A a = _args.d_a0;
          return a;
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

  // CREATORS
  explicit Ascii(Ascii0 _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Ascii> Ascii0_(Bool0 a0, Bool0 a1, Bool0 a2,
                                          Bool0 a3, Bool0 a4, Bool0 a5,
                                          Bool0 a6, Bool0 a7) {
      return std::shared_ptr<Ascii>(
          new Ascii(Ascii0{a0, a1, a2, a3, a4, a5, a6, a7}));
    }

    static std::unique_ptr<Ascii> Ascii0_uptr(Bool0 a0, Bool0 a1, Bool0 a2,
                                              Bool0 a3, Bool0 a4, Bool0 a5,
                                              Bool0 a6, Bool0 a7) {
      return std::unique_ptr<Ascii>(
          new Ascii(Ascii0{a0, a1, a2, a3, a4, a5, a6, a7}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) Sumbool
  ascii_dec(const std::shared_ptr<Ascii> &b) const {
    return std::visit(
        Overloaded{[&](const typename Ascii::Ascii0 _args) -> auto {
          Bool0 b0 = _args.d_a0;
          Bool0 b1 = _args.d_a1;
          Bool0 b2 = _args.d_a2;
          Bool0 b3 = _args.d_a3;
          Bool0 b4 = _args.d_a4;
          Bool0 b5 = _args.d_a5;
          Bool0 b6 = _args.d_a6;
          Bool0 b7 = _args.d_a7;
          return std::visit(
              Overloaded{[&](const typename Ascii::Ascii0 _args) -> Sumbool {
                Bool0 b8 = _args.d_a0;
                Bool0 b9 = _args.d_a1;
                Bool0 b10 = _args.d_a2;
                Bool0 b11 = _args.d_a3;
                Bool0 b12 = _args.d_a4;
                Bool0 b13 = _args.d_a5;
                Bool0 b14 = _args.d_a6;
                Bool0 b15 = _args.d_a7;
                return [&](void) {
                  switch (Bool::bool_dec(b0, b8)) {
                  case Sumbool::e_LEFT: {
                    return [&](void) {
                      switch (Bool::bool_dec(b1, b9)) {
                      case Sumbool::e_LEFT: {
                        return [&](void) {
                          switch (Bool::bool_dec(b2, b10)) {
                          case Sumbool::e_LEFT: {
                            return [&](void) {
                              switch (Bool::bool_dec(b3, b11)) {
                              case Sumbool::e_LEFT: {
                                return [&](void) {
                                  switch (Bool::bool_dec(b4, b12)) {
                                  case Sumbool::e_LEFT: {
                                    return [&](void) {
                                      switch (Bool::bool_dec(b5, b13)) {
                                      case Sumbool::e_LEFT: {
                                        return [&](void) {
                                          switch (Bool::bool_dec(b6, b14)) {
                                          case Sumbool::e_LEFT: {
                                            return [&](void) {
                                              switch (Bool::bool_dec(b7, b15)) {
                                              case Sumbool::e_LEFT: {
                                                return Sumbool::e_LEFT;
                                              }
                                              case Sumbool::e_RIGHT: {
                                                return Sumbool::e_RIGHT;
                                              }
                                              }
                                            }();
                                          }
                                          case Sumbool::e_RIGHT: {
                                            return Sumbool::e_RIGHT;
                                          }
                                          }
                                        }();
                                      }
                                      case Sumbool::e_RIGHT: {
                                        return Sumbool::e_RIGHT;
                                      }
                                      }
                                    }();
                                  }
                                  case Sumbool::e_RIGHT: {
                                    return Sumbool::e_RIGHT;
                                  }
                                  }
                                }();
                              }
                              case Sumbool::e_RIGHT: {
                                return Sumbool::e_RIGHT;
                              }
                              }
                            }();
                          }
                          case Sumbool::e_RIGHT: {
                            return Sumbool::e_RIGHT;
                          }
                          }
                        }();
                      }
                      case Sumbool::e_RIGHT: {
                        return Sumbool::e_RIGHT;
                      }
                      }
                    }();
                  }
                  case Sumbool::e_RIGHT: {
                    return Sumbool::e_RIGHT;
                  }
                  }
                }();
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

  // CREATORS
  explicit String(EmptyString _v) : d_v_(std::move(_v)) {}

  explicit String(String0 _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<String> EmptyString_() {
      return std::shared_ptr<String>(new String(EmptyString{}));
    }

    static std::shared_ptr<String> String0_(const std::shared_ptr<Ascii> &a0,
                                            const std::shared_ptr<String> &a1) {
      return std::shared_ptr<String>(new String(String0{a0, a1}));
    }

    static std::unique_ptr<String> EmptyString_uptr() {
      return std::unique_ptr<String>(new String(EmptyString{}));
    }

    static std::unique_ptr<String>
    String0_uptr(const std::shared_ptr<Ascii> &a0,
                 const std::shared_ptr<String> &a1) {
      return std::unique_ptr<String>(new String(String0{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<String> append(std::shared_ptr<String> s2) const {
    return std::visit(Overloaded{[&](const typename String::EmptyString _args)
                                     -> std::shared_ptr<String> { return s2; },
                                 [&](const typename String::String0 _args)
                                     -> std::shared_ptr<String> {
                                   std::shared_ptr<Ascii> c = _args.d_a0;
                                   std::shared_ptr<String> s1_ = _args.d_a1;
                                   return String::ctor::String0_(
                                       std::move(c),
                                       std::move(s1_)->append(s2));
                                 }},
                      this->v());
  }

  std::shared_ptr<Nat> length() const {
    return std::visit(
        Overloaded{
            [](const typename String::EmptyString _args)
                -> std::shared_ptr<Nat> { return Nat::ctor::O_(); },
            [](const typename String::String0 _args) -> std::shared_ptr<Nat> {
              std::shared_ptr<String> s_ = _args.d_a1;
              return Nat::ctor::S_(std::move(s_)->length());
            }},
        this->v());
  }
};

struct Levenshtein {
  struct edit {
    // TYPES
    struct Insertion {
      std::shared_ptr<Ascii> d_a0;
      std::shared_ptr<String> d_a1;
    };

    struct Deletion {
      std::shared_ptr<Ascii> d_a0;
      std::shared_ptr<String> d_a1;
    };

    struct Update {
      std::shared_ptr<Ascii> d_a0;
      std::shared_ptr<Ascii> d_a1;
      std::shared_ptr<String> d_a2;
    };

    using variant_t = std::variant<Insertion, Deletion, Update>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit edit(Insertion _v) : d_v_(std::move(_v)) {}

    explicit edit(Deletion _v) : d_v_(std::move(_v)) {}

    explicit edit(Update _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<edit>
      Insertion_(const std::shared_ptr<Ascii> &a0,
                 const std::shared_ptr<String> &a1) {
        return std::shared_ptr<edit>(new edit(Insertion{a0, a1}));
      }

      static std::shared_ptr<edit>
      Deletion_(const std::shared_ptr<Ascii> &a0,
                const std::shared_ptr<String> &a1) {
        return std::shared_ptr<edit>(new edit(Deletion{a0, a1}));
      }

      static std::shared_ptr<edit> Update_(const std::shared_ptr<Ascii> &a0,
                                           const std::shared_ptr<Ascii> &a1,
                                           const std::shared_ptr<String> &a2) {
        return std::shared_ptr<edit>(new edit(Update{a0, a1, a2}));
      }

      static std::unique_ptr<edit>
      Insertion_uptr(const std::shared_ptr<Ascii> &a0,
                     const std::shared_ptr<String> &a1) {
        return std::unique_ptr<edit>(new edit(Insertion{a0, a1}));
      }

      static std::unique_ptr<edit>
      Deletion_uptr(const std::shared_ptr<Ascii> &a0,
                    const std::shared_ptr<String> &a1) {
        return std::unique_ptr<edit>(new edit(Deletion{a0, a1}));
      }

      static std::unique_ptr<edit>
      Update_uptr(const std::shared_ptr<Ascii> &a0,
                  const std::shared_ptr<Ascii> &a1,
                  const std::shared_ptr<String> &a2) {
        return std::unique_ptr<edit>(new edit(Update{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1,
            MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<String>> F0,
            MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<String>> F1,
            MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<Ascii>,
                   std::shared_ptr<String>>
                F2>
  static T1 edit_rect(F0 &&f, F1 &&f0, F2 &&f1,
                      const std::shared_ptr<String> &_x,
                      const std::shared_ptr<String> &_x0,
                      const std::shared_ptr<edit> &e) {
    return std::visit(
        Overloaded{[&](const typename edit::Insertion _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args.d_a0;
                     std::shared_ptr<String> s = _args.d_a1;
                     return f(std::move(a), std::move(s));
                   },
                   [&](const typename edit::Deletion _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args.d_a0;
                     std::shared_ptr<String> s = _args.d_a1;
                     return f0(std::move(a), std::move(s));
                   },
                   [&](const typename edit::Update _args) -> T1 {
                     std::shared_ptr<Ascii> a_ = _args.d_a0;
                     std::shared_ptr<Ascii> a = _args.d_a1;
                     std::shared_ptr<String> s = _args.d_a2;
                     return f1(std::move(a_), std::move(a), std::move(s));
                   }},
        e->v());
  }

  template <typename T1,
            MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<String>> F0,
            MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<String>> F1,
            MapsTo<T1, std::shared_ptr<Ascii>, std::shared_ptr<Ascii>,
                   std::shared_ptr<String>>
                F2>
  static T1
  edit_rec(F0 &&f, F1 &&f0, F2 &&f1, const std::shared_ptr<String> &_x,
           const std::shared_ptr<String> &_x0, const std::shared_ptr<edit> &e) {
    return std::visit(
        Overloaded{[&](const typename edit::Insertion _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args.d_a0;
                     std::shared_ptr<String> s = _args.d_a1;
                     return f(std::move(a), std::move(s));
                   },
                   [&](const typename edit::Deletion _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args.d_a0;
                     std::shared_ptr<String> s = _args.d_a1;
                     return f0(std::move(a), std::move(s));
                   },
                   [&](const typename edit::Update _args) -> T1 {
                     std::shared_ptr<Ascii> a_ = _args.d_a0;
                     std::shared_ptr<Ascii> a = _args.d_a1;
                     std::shared_ptr<String> s = _args.d_a2;
                     return f1(std::move(a_), std::move(a), std::move(s));
                   }},
        e->v());
  }

  struct chain {
    // TYPES
    struct Empty {};

    struct Skip {
      std::shared_ptr<Ascii> d_a0;
      std::shared_ptr<String> d_a1;
      std::shared_ptr<String> d_a2;
      std::shared_ptr<Nat> d_a3;
      std::shared_ptr<chain> d_a4;
    };

    struct Change {
      std::shared_ptr<String> d_a0;
      std::shared_ptr<String> d_a1;
      std::shared_ptr<String> d_a2;
      std::shared_ptr<Nat> d_a3;
      std::shared_ptr<edit> d_a4;
      std::shared_ptr<chain> d_a5;
    };

    using variant_t = std::variant<Empty, Skip, Change>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit chain(Empty _v) : d_v_(std::move(_v)) {}

    explicit chain(Skip _v) : d_v_(std::move(_v)) {}

    explicit chain(Change _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<chain> Empty_() {
        return std::shared_ptr<chain>(new chain(Empty{}));
      }

      static std::shared_ptr<chain> Skip_(const std::shared_ptr<Ascii> &a0,
                                          const std::shared_ptr<String> &a1,
                                          const std::shared_ptr<String> &a2,
                                          const std::shared_ptr<Nat> &a3,
                                          const std::shared_ptr<chain> &a4) {
        return std::shared_ptr<chain>(new chain(Skip{a0, a1, a2, a3, a4}));
      }

      static std::shared_ptr<chain> Change_(const std::shared_ptr<String> &a0,
                                            const std::shared_ptr<String> &a1,
                                            const std::shared_ptr<String> &a2,
                                            const std::shared_ptr<Nat> &a3,
                                            const std::shared_ptr<edit> &a4,
                                            const std::shared_ptr<chain> &a5) {
        return std::shared_ptr<chain>(
            new chain(Change{a0, a1, a2, a3, a4, a5}));
      }

      static std::unique_ptr<chain> Empty_uptr() {
        return std::unique_ptr<chain>(new chain(Empty{}));
      }

      static std::unique_ptr<chain> Skip_uptr(
          const std::shared_ptr<Ascii> &a0, const std::shared_ptr<String> &a1,
          const std::shared_ptr<String> &a2, const std::shared_ptr<Nat> &a3,
          const std::shared_ptr<chain> &a4) {
        return std::unique_ptr<chain>(new chain(Skip{a0, a1, a2, a3, a4}));
      }

      static std::unique_ptr<chain> Change_uptr(
          const std::shared_ptr<String> &a0, const std::shared_ptr<String> &a1,
          const std::shared_ptr<String> &a2, const std::shared_ptr<Nat> &a3,
          const std::shared_ptr<edit> &a4, const std::shared_ptr<chain> &a5) {
        return std::unique_ptr<chain>(
            new chain(Change{a0, a1, a2, a3, a4, a5}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
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
                     std::shared_ptr<Ascii> a = _args.d_a0;
                     std::shared_ptr<String> s = _args.d_a1;
                     std::shared_ptr<String> t = _args.d_a2;
                     std::shared_ptr<Nat> n = _args.d_a3;
                     std::shared_ptr<chain> c0 = _args.d_a4;
                     return f0(std::move(a), s, t, n, c0,
                               chain_rect<T1>(f, f0, f1, s, t, n, c0));
                   },
                   [&](const typename chain::Change _args) -> T1 {
                     std::shared_ptr<String> s = _args.d_a0;
                     std::shared_ptr<String> t = _args.d_a1;
                     std::shared_ptr<String> u = _args.d_a2;
                     std::shared_ptr<Nat> n = _args.d_a3;
                     std::shared_ptr<edit> e = _args.d_a4;
                     std::shared_ptr<chain> c0 = _args.d_a5;
                     return f1(std::move(s), t, u, n, std::move(e), c0,
                               chain_rect<T1>(f, f0, f1, t, u, n, c0));
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
                     std::shared_ptr<Ascii> a = _args.d_a0;
                     std::shared_ptr<String> s = _args.d_a1;
                     std::shared_ptr<String> t = _args.d_a2;
                     std::shared_ptr<Nat> n = _args.d_a3;
                     std::shared_ptr<chain> c0 = _args.d_a4;
                     return f0(std::move(a), s, t, n, c0,
                               chain_rec<T1>(f, f0, f1, s, t, n, c0));
                   },
                   [&](const typename chain::Change _args) -> T1 {
                     std::shared_ptr<String> s = _args.d_a0;
                     std::shared_ptr<String> t = _args.d_a1;
                     std::shared_ptr<String> u = _args.d_a2;
                     std::shared_ptr<Nat> n = _args.d_a3;
                     std::shared_ptr<edit> e = _args.d_a4;
                     std::shared_ptr<chain> c0 = _args.d_a5;
                     return f1(std::move(s), t, u, n, std::move(e), c0,
                               chain_rec<T1>(f, f0, f1, t, u, n, c0));
                   }},
        c->v());
  }

  static std::shared_ptr<chain> same_chain(const std::shared_ptr<String> &s);
  static std::shared_ptr<chain> insert_chain(std::shared_ptr<Ascii> c,
                                             std::shared_ptr<String> s1,
                                             std::shared_ptr<String> s2,
                                             std::shared_ptr<Nat> n,
                                             std::shared_ptr<chain> c0);

  template <typename T1>
  static T1 _inserts_chain_F(const std::shared_ptr<String> &s) {
    return std::visit(
        Overloaded{[](const typename String::EmptyString _args) -> T1 {
                     return chain::ctor::Empty_();
                   },
                   [](const typename String::String0 _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args.d_a0;
                     std::shared_ptr<String> s0 = _args.d_a1;
                     return chain::ctor::Skip_(std::move(a), s0, s0,
                                               Nat::ctor::O_(),
                                               _inserts_chain_F<T1>(s0));
                   }},
        s->v());
  }

  static std::shared_ptr<chain>
  inserts_chain(const std::shared_ptr<String> &s1,
                const std::shared_ptr<String> &s2);
  static std::shared_ptr<chain>
  inserts_chain_empty(const std::shared_ptr<String> &s);
  static std::shared_ptr<chain> delete_chain(std::shared_ptr<Ascii> c,
                                             std::shared_ptr<String> s1,
                                             std::shared_ptr<String> s2,
                                             std::shared_ptr<Nat> n,
                                             std::shared_ptr<chain> c0);
  static std::shared_ptr<chain>
  deletes_chain(const std::shared_ptr<String> &s1,
                const std::shared_ptr<String> &s2);
  static std::shared_ptr<chain>
  deletes_chain_empty(const std::shared_ptr<String> &s);
  static std::shared_ptr<chain>
  update_chain(std::shared_ptr<Ascii> c, std::shared_ptr<Ascii> c_,
               std::shared_ptr<String> s1, std::shared_ptr<String> s2,
               std::shared_ptr<Nat> n, std::shared_ptr<chain> c0);
  static std::shared_ptr<chain>
  aux_insert(const std::shared_ptr<String> &_x,
             const std::shared_ptr<String> &_x0, std::shared_ptr<Ascii> x,
             std::shared_ptr<String> xs, const std::shared_ptr<Ascii> &y,
             const std::shared_ptr<String> &ys, const std::shared_ptr<Nat> &n,
             const std::shared_ptr<chain> &r1);
  static std::shared_ptr<chain>
  aux_delete(const std::shared_ptr<String> &_x,
             const std::shared_ptr<String> &_x0,
             const std::shared_ptr<Ascii> &x, const std::shared_ptr<String> &xs,
             std::shared_ptr<Ascii> y, std::shared_ptr<String> ys,
             const std::shared_ptr<Nat> &n, const std::shared_ptr<chain> &r2);
  static std::shared_ptr<chain>
  aux_update(const std::shared_ptr<String> &_x,
             const std::shared_ptr<String> &_x0,
             const std::shared_ptr<Ascii> &x, const std::shared_ptr<String> &xs,
             const std::shared_ptr<Ascii> &y, const std::shared_ptr<String> &ys,
             const std::shared_ptr<Nat> &n, const std::shared_ptr<chain> &r3);
  static std::shared_ptr<chain>
  aux_eq_char(const std::shared_ptr<String> &_x,
              const std::shared_ptr<String> &_x0,
              const std::shared_ptr<Ascii> &_x1, std::shared_ptr<String> xs,
              std::shared_ptr<Ascii> y, std::shared_ptr<String> ys,
              std::shared_ptr<Nat> n, std::shared_ptr<chain> c);
  static std::shared_ptr<chain>
  aux_both_empty(const std::shared_ptr<String> &_x,
                 const std::shared_ptr<String> &_x0);

  template <typename T1, MapsTo<std::shared_ptr<Nat>, T1> F3>
  static T1 min3_app(const T1 x, const T1 y, const T1 z, F3 &&f) {
    std::shared_ptr<Nat> n1 = f(x);
    std::shared_ptr<Nat> n2 = f(y);
    std::shared_ptr<Nat> n3 = f(z);
    return [&](void) {
      switch (n1->leb(n2)) {
      case Bool0::e_TRUE0: {
        return [&](void) {
          switch (std::move(n1)->leb(std::move(n3))) {
          case Bool0::e_TRUE0: {
            return x;
          }
          case Bool0::e_FALSE0: {
            return z;
          }
          }
        }();
      }
      case Bool0::e_FALSE0: {
        return [&](void) {
          switch (std::move(n2)->leb(std::move(n3))) {
          case Bool0::e_TRUE0: {
            return y;
          }
          case Bool0::e_FALSE0: {
            return z;
          }
          }
        }();
      }
      }
    }();
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
