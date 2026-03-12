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

enum class bool0 { true0, false0 };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> _a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit Nat(O _v) : v_(std::move(_v)) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

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
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool0 leb(const std::shared_ptr<Nat> &m) const {
    return std::visit(
        Overloaded{
            [](const typename Nat::O _args) -> bool0 { return bool0::true0; },
            [&](const typename Nat::S _args) -> bool0 {
              std::shared_ptr<Nat> n_ = _args._a0;
              return std::visit(
                  Overloaded{[](const typename Nat::O _args) -> bool0 {
                               return bool0::false0;
                             },
                             [&](const typename Nat::S _args) -> bool0 {
                               std::shared_ptr<Nat> m_ = _args._a0;
                               return std::move(n_)->leb(std::move(m_));
                             }},
                  m->v());
            }},
        this->v());
  }
};

template <typename A, typename P> struct SigT {
  // TYPES
  struct existT {
    A _a0;
    P _a1;
  };

  using variant_t = std::variant<existT>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit SigT(existT _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<SigT<A, P>> existT_(A a0, P a1) {
      return std::shared_ptr<SigT<A, P>>(new SigT<A, P>(existT{a0, a1}));
    }

    static std::unique_ptr<SigT<A, P>> existT_uptr(A a0, P a1) {
      return std::unique_ptr<SigT<A, P>>(new SigT<A, P>(existT{a0, a1}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  A projT1() const {
    return std::visit(
        Overloaded{[](const typename SigT<A, P>::existT _args) -> A {
          A a = _args._a0;
          return a;
        }},
        this->v());
  }
};
enum class sumbool { left, right };

struct Bool {
  static sumbool bool_dec(const bool0 b1, const bool0 b2);
};

struct Ascii {
  // TYPES
  struct Ascii0 {
    bool0 _a0;
    bool0 _a1;
    bool0 _a2;
    bool0 _a3;
    bool0 _a4;
    bool0 _a5;
    bool0 _a6;
    bool0 _a7;
  };

  using variant_t = std::variant<Ascii0>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit Ascii(Ascii0 _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Ascii> Ascii0_(bool0 a0, bool0 a1, bool0 a2,
                                          bool0 a3, bool0 a4, bool0 a5,
                                          bool0 a6, bool0 a7) {
      return std::shared_ptr<Ascii>(
          new Ascii(Ascii0{a0, a1, a2, a3, a4, a5, a6, a7}));
    }

    static std::unique_ptr<Ascii> Ascii0_uptr(bool0 a0, bool0 a1, bool0 a2,
                                              bool0 a3, bool0 a4, bool0 a5,
                                              bool0 a6, bool0 a7) {
      return std::unique_ptr<Ascii>(
          new Ascii(Ascii0{a0, a1, a2, a3, a4, a5, a6, a7}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  sumbool ascii_dec(const std::shared_ptr<Ascii> &b) const {
    return std::visit(
        Overloaded{[&](const typename Ascii::Ascii0 _args) -> auto {
          bool0 b0 = _args._a0;
          bool0 b1 = _args._a1;
          bool0 b2 = _args._a2;
          bool0 b3 = _args._a3;
          bool0 b4 = _args._a4;
          bool0 b5 = _args._a5;
          bool0 b6 = _args._a6;
          bool0 b7 = _args._a7;
          return std::visit(
              Overloaded{[&](const typename Ascii::Ascii0 _args) -> sumbool {
                bool0 b8 = _args._a0;
                bool0 b9 = _args._a1;
                bool0 b10 = _args._a2;
                bool0 b11 = _args._a3;
                bool0 b12 = _args._a4;
                bool0 b13 = _args._a5;
                bool0 b14 = _args._a6;
                bool0 b15 = _args._a7;
                return [&](void) {
                  switch (Bool::bool_dec(b0, b8)) {
                  case sumbool::left: {
                    return [&](void) {
                      switch (Bool::bool_dec(b1, b9)) {
                      case sumbool::left: {
                        return [&](void) {
                          switch (Bool::bool_dec(b2, b10)) {
                          case sumbool::left: {
                            return [&](void) {
                              switch (Bool::bool_dec(b3, b11)) {
                              case sumbool::left: {
                                return [&](void) {
                                  switch (Bool::bool_dec(b4, b12)) {
                                  case sumbool::left: {
                                    return [&](void) {
                                      switch (Bool::bool_dec(b5, b13)) {
                                      case sumbool::left: {
                                        return [&](void) {
                                          switch (Bool::bool_dec(b6, b14)) {
                                          case sumbool::left: {
                                            return [&](void) {
                                              switch (Bool::bool_dec(b7, b15)) {
                                              case sumbool::left: {
                                                return sumbool::left;
                                              }
                                              case sumbool::right: {
                                                return sumbool::right;
                                              }
                                              }
                                            }();
                                          }
                                          case sumbool::right: {
                                            return sumbool::right;
                                          }
                                          }
                                        }();
                                      }
                                      case sumbool::right: {
                                        return sumbool::right;
                                      }
                                      }
                                    }();
                                  }
                                  case sumbool::right: {
                                    return sumbool::right;
                                  }
                                  }
                                }();
                              }
                              case sumbool::right: {
                                return sumbool::right;
                              }
                              }
                            }();
                          }
                          case sumbool::right: {
                            return sumbool::right;
                          }
                          }
                        }();
                      }
                      case sumbool::right: {
                        return sumbool::right;
                      }
                      }
                    }();
                  }
                  case sumbool::right: {
                    return sumbool::right;
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
    std::shared_ptr<Ascii> _a0;
    std::shared_ptr<String> _a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit String(EmptyString _v) : v_(std::move(_v)) {}

  explicit String(String0 _v) : v_(std::move(_v)) {}

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
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  std::shared_ptr<String> append(std::shared_ptr<String> s2) const {
    return std::visit(Overloaded{[&](const typename String::EmptyString _args)
                                     -> std::shared_ptr<String> { return s2; },
                                 [&](const typename String::String0 _args)
                                     -> std::shared_ptr<String> {
                                   std::shared_ptr<Ascii> c = _args._a0;
                                   std::shared_ptr<String> s1_ = _args._a1;
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
              std::shared_ptr<String> s_ = _args._a1;
              return Nat::ctor::S_(std::move(s_)->length());
            }},
        this->v());
  }
};

struct Levenshtein {
  struct edit {
    // TYPES
    struct insertion {
      std::shared_ptr<Ascii> _a0;
      std::shared_ptr<String> _a1;
    };

    struct deletion {
      std::shared_ptr<Ascii> _a0;
      std::shared_ptr<String> _a1;
    };

    struct update {
      std::shared_ptr<Ascii> _a0;
      std::shared_ptr<Ascii> _a1;
      std::shared_ptr<String> _a2;
    };

    using variant_t = std::variant<insertion, deletion, update>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit edit(insertion _v) : v_(std::move(_v)) {}

    explicit edit(deletion _v) : v_(std::move(_v)) {}

    explicit edit(update _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<edit>
      insertion_(const std::shared_ptr<Ascii> &a0,
                 const std::shared_ptr<String> &a1) {
        return std::shared_ptr<edit>(new edit(insertion{a0, a1}));
      }

      static std::shared_ptr<edit>
      deletion_(const std::shared_ptr<Ascii> &a0,
                const std::shared_ptr<String> &a1) {
        return std::shared_ptr<edit>(new edit(deletion{a0, a1}));
      }

      static std::shared_ptr<edit> update_(const std::shared_ptr<Ascii> &a0,
                                           const std::shared_ptr<Ascii> &a1,
                                           const std::shared_ptr<String> &a2) {
        return std::shared_ptr<edit>(new edit(update{a0, a1, a2}));
      }

      static std::unique_ptr<edit>
      insertion_uptr(const std::shared_ptr<Ascii> &a0,
                     const std::shared_ptr<String> &a1) {
        return std::unique_ptr<edit>(new edit(insertion{a0, a1}));
      }

      static std::unique_ptr<edit>
      deletion_uptr(const std::shared_ptr<Ascii> &a0,
                    const std::shared_ptr<String> &a1) {
        return std::unique_ptr<edit>(new edit(deletion{a0, a1}));
      }

      static std::unique_ptr<edit>
      update_uptr(const std::shared_ptr<Ascii> &a0,
                  const std::shared_ptr<Ascii> &a1,
                  const std::shared_ptr<String> &a2) {
        return std::unique_ptr<edit>(new edit(update{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
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
        Overloaded{[&](const typename edit::insertion _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args._a0;
                     std::shared_ptr<String> s = _args._a1;
                     return f(std::move(a), std::move(s));
                   },
                   [&](const typename edit::deletion _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args._a0;
                     std::shared_ptr<String> s = _args._a1;
                     return f0(std::move(a), std::move(s));
                   },
                   [&](const typename edit::update _args) -> T1 {
                     std::shared_ptr<Ascii> a_ = _args._a0;
                     std::shared_ptr<Ascii> a = _args._a1;
                     std::shared_ptr<String> s = _args._a2;
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
        Overloaded{[&](const typename edit::insertion _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args._a0;
                     std::shared_ptr<String> s = _args._a1;
                     return f(std::move(a), std::move(s));
                   },
                   [&](const typename edit::deletion _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args._a0;
                     std::shared_ptr<String> s = _args._a1;
                     return f0(std::move(a), std::move(s));
                   },
                   [&](const typename edit::update _args) -> T1 {
                     std::shared_ptr<Ascii> a_ = _args._a0;
                     std::shared_ptr<Ascii> a = _args._a1;
                     std::shared_ptr<String> s = _args._a2;
                     return f1(std::move(a_), std::move(a), std::move(s));
                   }},
        e->v());
  }

  struct chain {
    // TYPES
    struct empty {};

    struct skip {
      std::shared_ptr<Ascii> _a0;
      std::shared_ptr<String> _a1;
      std::shared_ptr<String> _a2;
      std::shared_ptr<Nat> _a3;
      std::shared_ptr<chain> _a4;
    };

    struct change {
      std::shared_ptr<String> _a0;
      std::shared_ptr<String> _a1;
      std::shared_ptr<String> _a2;
      std::shared_ptr<Nat> _a3;
      std::shared_ptr<edit> _a4;
      std::shared_ptr<chain> _a5;
    };

    using variant_t = std::variant<empty, skip, change>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit chain(empty _v) : v_(std::move(_v)) {}

    explicit chain(skip _v) : v_(std::move(_v)) {}

    explicit chain(change _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<chain> empty_() {
        return std::shared_ptr<chain>(new chain(empty{}));
      }

      static std::shared_ptr<chain> skip_(const std::shared_ptr<Ascii> &a0,
                                          const std::shared_ptr<String> &a1,
                                          const std::shared_ptr<String> &a2,
                                          const std::shared_ptr<Nat> &a3,
                                          const std::shared_ptr<chain> &a4) {
        return std::shared_ptr<chain>(new chain(skip{a0, a1, a2, a3, a4}));
      }

      static std::shared_ptr<chain> change_(const std::shared_ptr<String> &a0,
                                            const std::shared_ptr<String> &a1,
                                            const std::shared_ptr<String> &a2,
                                            const std::shared_ptr<Nat> &a3,
                                            const std::shared_ptr<edit> &a4,
                                            const std::shared_ptr<chain> &a5) {
        return std::shared_ptr<chain>(
            new chain(change{a0, a1, a2, a3, a4, a5}));
      }

      static std::unique_ptr<chain> empty_uptr() {
        return std::unique_ptr<chain>(new chain(empty{}));
      }

      static std::unique_ptr<chain> skip_uptr(
          const std::shared_ptr<Ascii> &a0, const std::shared_ptr<String> &a1,
          const std::shared_ptr<String> &a2, const std::shared_ptr<Nat> &a3,
          const std::shared_ptr<chain> &a4) {
        return std::unique_ptr<chain>(new chain(skip{a0, a1, a2, a3, a4}));
      }

      static std::unique_ptr<chain> change_uptr(
          const std::shared_ptr<String> &a0, const std::shared_ptr<String> &a1,
          const std::shared_ptr<String> &a2, const std::shared_ptr<Nat> &a3,
          const std::shared_ptr<edit> &a4, const std::shared_ptr<chain> &a5) {
        return std::unique_ptr<chain>(
            new chain(change{a0, a1, a2, a3, a4, a5}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
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
        Overloaded{[&](const typename chain::empty _args) -> T1 { return f; },
                   [&](const typename chain::skip _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args._a0;
                     std::shared_ptr<String> s = _args._a1;
                     std::shared_ptr<String> t = _args._a2;
                     std::shared_ptr<Nat> n = _args._a3;
                     std::shared_ptr<chain> c0 = _args._a4;
                     return f0(std::move(a), s, t, n, c0,
                               chain_rect<T1>(f, f0, f1, s, t, n, c0));
                   },
                   [&](const typename chain::change _args) -> T1 {
                     std::shared_ptr<String> s = _args._a0;
                     std::shared_ptr<String> t = _args._a1;
                     std::shared_ptr<String> u = _args._a2;
                     std::shared_ptr<Nat> n = _args._a3;
                     std::shared_ptr<edit> e = _args._a4;
                     std::shared_ptr<chain> c0 = _args._a5;
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
        Overloaded{[&](const typename chain::empty _args) -> T1 { return f; },
                   [&](const typename chain::skip _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args._a0;
                     std::shared_ptr<String> s = _args._a1;
                     std::shared_ptr<String> t = _args._a2;
                     std::shared_ptr<Nat> n = _args._a3;
                     std::shared_ptr<chain> c0 = _args._a4;
                     return f0(std::move(a), s, t, n, c0,
                               chain_rec<T1>(f, f0, f1, s, t, n, c0));
                   },
                   [&](const typename chain::change _args) -> T1 {
                     std::shared_ptr<String> s = _args._a0;
                     std::shared_ptr<String> t = _args._a1;
                     std::shared_ptr<String> u = _args._a2;
                     std::shared_ptr<Nat> n = _args._a3;
                     std::shared_ptr<edit> e = _args._a4;
                     std::shared_ptr<chain> c0 = _args._a5;
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
                     return chain::ctor::empty_();
                   },
                   [](const typename String::String0 _args) -> T1 {
                     std::shared_ptr<Ascii> a = _args._a0;
                     std::shared_ptr<String> s0 = _args._a1;
                     return chain::ctor::skip_(std::move(a), s0, s0,
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
      case bool0::true0: {
        return [&](void) {
          switch (std::move(n1)->leb(std::move(n3))) {
          case bool0::true0: {
            return x;
          }
          case bool0::false0: {
            return z;
          }
          }
        }();
      }
      case bool0::false0: {
        return [&](void) {
          switch (std::move(n2)->leb(std::move(n3))) {
          case bool0::true0: {
            return y;
          }
          case bool0::false0: {
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
