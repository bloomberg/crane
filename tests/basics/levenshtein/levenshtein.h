#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Bool0 {
  struct bool0 {
  public:
    struct true0 {};
    struct false0 {};
    using variant_t = std::variant<true0, false0>;

  private:
    variant_t v_;
    explicit bool0(true0 x) : v_(std::move(x)) {}
    explicit bool0(false0 x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Bool0::bool0> true0_() {
        return std::shared_ptr<Bool0::bool0>(new Bool0::bool0(true0{}));
      }
      static std::shared_ptr<Bool0::bool0> false0_() {
        return std::shared_ptr<Bool0::bool0>(new Bool0::bool0(false0{}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct Nat {
  struct nat {
  public:
    struct O {};
    struct S {
      std::shared_ptr<Nat::nat> _a0;
    };
    using variant_t = std::variant<O, S>;

  private:
    variant_t v_;
    explicit nat(O x) : v_(std::move(x)) {}
    explicit nat(S x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Nat::nat> O_() {
        return std::shared_ptr<Nat::nat>(new Nat::nat(O{}));
      }
      static std::shared_ptr<Nat::nat> S_(const std::shared_ptr<Nat::nat> &a0) {
        return std::shared_ptr<Nat::nat>(new Nat::nat(S{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct SigT {
  template <typename A, typename P> struct sigT {
  public:
    struct existT {
      A _a0;
      P _a1;
    };
    using variant_t = std::variant<existT>;

  private:
    variant_t v_;
    explicit sigT(existT x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<SigT::sigT<A, P>> existT_(A a0, P a1) {
        return std::shared_ptr<SigT::sigT<A, P>>(
            new SigT::sigT<A, P>(existT{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    A projT1() const {
      return std::visit(
          Overloaded{[&](const typename SigT::sigT<A, P>::existT _args) -> A {
            A a = _args._a0;
            return a;
          }},
          this->v());
    }
  };
};

struct Sumbool {
  struct sumbool {
  public:
    struct left {};
    struct right {};
    using variant_t = std::variant<left, right>;

  private:
    variant_t v_;
    explicit sumbool(left x) : v_(std::move(x)) {}
    explicit sumbool(right x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Sumbool::sumbool> left_() {
        return std::shared_ptr<Sumbool::sumbool>(new Sumbool::sumbool(left{}));
      }
      static std::shared_ptr<Sumbool::sumbool> right_() {
        return std::shared_ptr<Sumbool::sumbool>(new Sumbool::sumbool(right{}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

std::shared_ptr<Bool0::bool0> leb(const std::shared_ptr<Nat::nat> &n,
                                  const std::shared_ptr<Nat::nat> &m);

std::shared_ptr<Sumbool::sumbool>
bool_dec(const std::shared_ptr<Bool0::bool0> &b1,
         const std::shared_ptr<Bool0::bool0> &b2);

struct Ascii {
  struct ascii {
  public:
    struct Ascii {
      std::shared_ptr<Bool0::bool0> _a0;
      std::shared_ptr<Bool0::bool0> _a1;
      std::shared_ptr<Bool0::bool0> _a2;
      std::shared_ptr<Bool0::bool0> _a3;
      std::shared_ptr<Bool0::bool0> _a4;
      std::shared_ptr<Bool0::bool0> _a5;
      std::shared_ptr<Bool0::bool0> _a6;
      std::shared_ptr<Bool0::bool0> _a7;
    };
    using variant_t = std::variant<Ascii>;

  private:
    variant_t v_;
    explicit ascii(Ascii x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Ascii::ascii>
      Ascii_(const std::shared_ptr<Bool0::bool0> &a0,
             const std::shared_ptr<Bool0::bool0> &a1,
             const std::shared_ptr<Bool0::bool0> &a2,
             const std::shared_ptr<Bool0::bool0> &a3,
             const std::shared_ptr<Bool0::bool0> &a4,
             const std::shared_ptr<Bool0::bool0> &a5,
             const std::shared_ptr<Bool0::bool0> &a6,
             const std::shared_ptr<Bool0::bool0> &a7) {
        return std::shared_ptr<Ascii::ascii>(
            new Ascii::ascii(Ascii{a0, a1, a2, a3, a4, a5, a6, a7}));
      }
    };
    const variant_t &v() const { return v_; }
    std::shared_ptr<Sumbool::sumbool>
    ascii_dec(const std::shared_ptr<Ascii::ascii> &b) const {
      return std::visit(
          Overloaded{[&](const typename Ascii::ascii::Ascii _args) -> T1 {
            std::shared_ptr<Bool0::bool0> b0 = _args._a0;
            std::shared_ptr<Bool0::bool0> b1 = _args._a1;
            std::shared_ptr<Bool0::bool0> b2 = _args._a2;
            std::shared_ptr<Bool0::bool0> b3 = _args._a3;
            std::shared_ptr<Bool0::bool0> b4 = _args._a4;
            std::shared_ptr<Bool0::bool0> b5 = _args._a5;
            std::shared_ptr<Bool0::bool0> b6 = _args._a6;
            std::shared_ptr<Bool0::bool0> b7 = _args._a7;
            return std::visit(
                Overloaded{[&](const typename Ascii::ascii::Ascii _args) -> std::
                                                                             shared_ptr<
                                                                                 Sumbool::
                                                                                     sumbool> {
                                                                               std::shared_ptr<
                                                                                   Bool0::
                                                                                       bool0>
                                                                                   b8 =
                                                                                       _args
                                                                                           ._a0;
                                                                               std::shared_ptr<
                                                                                   Bool0::
                                                                                       bool0>
                                                                                   b9 =
                                                                                       _args
                                                                                           ._a1;
                                                                               std::shared_ptr<
                                                                                   Bool0::
                                                                                       bool0>
                                                                                   b10 =
                                                                                       _args
                                                                                           ._a2;
                                                                               std::shared_ptr<
                                                                                   Bool0::
                                                                                       bool0>
                                                                                   b11 =
                                                                                       _args
                                                                                           ._a3;
                                                                               std::shared_ptr<
                                                                                   Bool0::
                                                                                       bool0>
                                                                                   b12 =
                                                                                       _args
                                                                                           ._a4;
                                                                               std::shared_ptr<
                                                                                   Bool0::
                                                                                       bool0>
                                                                                   b13 =
                                                                                       _args
                                                                                           ._a5;
                                                                               std::shared_ptr<
                                                                                   Bool0::
                                                                                       bool0>
                                                                                   b14 =
                                                                                       _args
                                                                                           ._a6;
                                                                               std::shared_ptr<
                                                                                   Bool0::
                                                                                       bool0>
                                                                                   b15 =
                                                                                       _args
                                                                                           ._a7;
                                                                               return std::visit(
                                                                                   Overloaded{
                                                                                       [&](const typename Sumbool::
                                                                                               sumbool::left
                                                                                                   _args)
                                                                                           -> T1 {
                                                                                         return std::visit(
                                                                                             Overloaded{
                                                                                                 [&](const typename Sumbool::
                                                                                                         sumbool::left
                                                                                                             _args)
                                                                                                     -> T1 {
                                                                                                   return std::visit(
                                                                                                       Overloaded{
                                                                                                           [&](const typename Sumbool::
                                                                                                                   sumbool::left
                                                                                                                       _args)
                                                                                                               -> T1 {
                                                                                                             return std::visit(
                                                                                                                 Overloaded{[&](const typename Sumbool::
                                                                                                                                    sumbool::left
                                                                                                                                        _args)
                                                                                                                                -> T1 {
                                                                                                                              return std::visit(
                                                                                                                                  Overloaded{
                                                                                                                                      [&](const typename Sumbool::
                                                                                                                                              sumbool::left
                                                                                                                                                  _args)
                                                                                                                                          -> T1 {
                                                                                                                                        return std::visit(
                                                                                                                                            Overloaded{
                                                                                                                                                [&](const typename Sumbool::sumbool::left _args) -> T1 {
                                                                                                                                                  return std::
                                                                                                                                                      visit(Overloaded{[&](const typename Sumbool::
                                                                                                                                                                               sumbool::left
                                                                                                                                                                                   _args)
                                                                                                                                                                           -> T1 {
                                                                                                                                                                         return std::
                                                                                                                                                                             visit(Overloaded{[&](const typename Sumbool::
                                                                                                                                                                                                      sumbool::left
                                                                                                                                                                                                          _args)
                                                                                                                                                                                                  -> T1 {
                                                                                                                                                                                                return Sumbool::
                                                                                                                                                                                                    sumbool::ctor::
                                                                                                                                                                                                        left_();
                                                                                                                                                                                              },
                                                                                                                                                                                              [&](const typename Sumbool::
                                                                                                                                                                                                      sumbool::right
                                                                                                                                                                                                          _args)
                                                                                                                                                                                                  -> T1 {
                                                                                                                                                                                                return Sumbool::
                                                                                                                                                                                                    sumbool::ctor::
                                                                                                                                                                                                        right_();
                                                                                                                                                                                              }},
                                                                                                                                                                                   bool_dec(
                                                                                                                                                                                       b7,
                                                                                                                                                                                       b15)
                                                                                                                                                                                       ->v());
                                                                                                                                                                       },
                                                                                                                                                                       [&](const typename Sumbool::sumbool::right _args) -> T1 {
                                                                                                                                                                         return Sumbool::
                                                                                                                                                                             sumbool::ctor::
                                                                                                                                                                                 right_();
                                                                                                                                                                       }},
                                                                                                                                                            bool_dec(
                                                                                                                                                                b6,
                                                                                                                                                                b14)
                                                                                                                                                                ->v());
                                                                                                                                                },
                                                                                                                                                [&](const typename Sumbool::
                                                                                                                                                        sumbool::right
                                                                                                                                                            _args)
                                                                                                                                                    -> T1 {
                                                                                                                                                  return Sumbool::
                                                                                                                                                      sumbool::ctor::
                                                                                                                                                          right_();
                                                                                                                                                }},
                                                                                                                                            bool_dec(
                                                                                                                                                b5,
                                                                                                                                                b13)
                                                                                                                                                ->v());
                                                                                                                                      },
                                                                                                                                      [&](const typename Sumbool::
                                                                                                                                              sumbool::right
                                                                                                                                                  _args)
                                                                                                                                          -> T1 {
                                                                                                                                        return Sumbool::
                                                                                                                                            sumbool::ctor::
                                                                                                                                                right_();
                                                                                                                                      }},
                                                                                                                                  bool_dec(
                                                                                                                                      b4,
                                                                                                                                      b12)
                                                                                                                                      ->v());
                                                                                                                            },
                                                                                                                            [&](const typename Sumbool::
                                                                                                                                    sumbool::right
                                                                                                                                        _args)
                                                                                                                                -> T1 {
                                                                                                                              return Sumbool::
                                                                                                                                  sumbool::ctor::
                                                                                                                                      right_();
                                                                                                                            }},
                                                                                                                 bool_dec(
                                                                                                                     b3,
                                                                                                                     b11)
                                                                                                                     ->v());
                                                                                                           },
                                                                                                           [&](const typename Sumbool::
                                                                                                                   sumbool::right
                                                                                                                       _args) -> T1 {
                                                                                                             return Sumbool::
                                                                                                                 sumbool::ctor::
                                                                                                                     right_();
                                                                                                           }},
                                                                                                       bool_dec(
                                                                                                           b2,
                                                                                                           b10)
                                                                                                           ->v());
                                                                                                 },
                                                                                                 [&](const typename Sumbool::
                                                                                                         sumbool::right
                                                                                                             _args)
                                                                                                     -> T1 {
                                                                                                   return Sumbool::
                                                                                                       sumbool::ctor::
                                                                                                           right_();
                                                                                                 }},
                                                                                             bool_dec(
                                                                                                 b1,
                                                                                                 b9)
                                                                                                 ->v());
                                                                                       },
                                                                                       [&](const typename Sumbool::
                                                                                               sumbool::right
                                                                                                   _args)
                                                                                           -> T1 {
                                                                                         return Sumbool::
                                                                                             sumbool::ctor::
                                                                                                 right_();
                                                                                       }},
                                                                                   bool_dec(
                                                                                       b0,
                                                                                       b8)
                                                                                       ->v());
                                                                             }},
                b->v());
          }},
          this->v());
    }
  };
};

struct String {
  struct string {
  public:
    struct EmptyString {};
    struct String {
      std::shared_ptr<Ascii::ascii> _a0;
      std::shared_ptr<String::string> _a1;
    };
    using variant_t = std::variant<EmptyString, String>;

  private:
    variant_t v_;
    explicit string(EmptyString x) : v_(std::move(x)) {}
    explicit string(String x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<String::string> EmptyString_() {
        return std::shared_ptr<String::string>(
            new String::string(EmptyString{}));
      }
      static std::shared_ptr<String::string>
      String_(const std::shared_ptr<Ascii::ascii> &a0,
              const std::shared_ptr<String::string> &a1) {
        return std::shared_ptr<String::string>(
            new String::string(String{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    std::shared_ptr<Nat::nat> length() const {
      return std::visit(
          Overloaded{
              [&](const typename String::string::EmptyString _args)
                  -> std::shared_ptr<Nat::nat> { return Nat::nat::ctor::O_(); },
              [&](const typename String::string::String _args)
                  -> std::shared_ptr<Nat::nat> {
                std::shared_ptr<String::string> s_ = _args._a1;
                return Nat::nat::ctor::S_(s_->length());
              }},
          this->v());
    }
  };
};

struct Edit {
  struct edit {
  public:
    struct insertion {
      std::shared_ptr<Ascii::ascii> _a0;
      std::shared_ptr<String::string> _a1;
    };
    struct deletion {
      std::shared_ptr<Ascii::ascii> _a0;
      std::shared_ptr<String::string> _a1;
    };
    struct update {
      std::shared_ptr<Ascii::ascii> _a0;
      std::shared_ptr<Ascii::ascii> _a1;
      std::shared_ptr<String::string> _a2;
    };
    using variant_t = std::variant<insertion, deletion, update>;

  private:
    variant_t v_;
    explicit edit(insertion x) : v_(std::move(x)) {}
    explicit edit(deletion x) : v_(std::move(x)) {}
    explicit edit(update x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Edit::edit>
      insertion_(const std::shared_ptr<Ascii::ascii> &a0,
                 const std::shared_ptr<String::string> &a1) {
        return std::shared_ptr<Edit::edit>(new Edit::edit(insertion{a0, a1}));
      }
      static std::shared_ptr<Edit::edit>
      deletion_(const std::shared_ptr<Ascii::ascii> &a0,
                const std::shared_ptr<String::string> &a1) {
        return std::shared_ptr<Edit::edit>(new Edit::edit(deletion{a0, a1}));
      }
      static std::shared_ptr<Edit::edit>
      update_(const std::shared_ptr<Ascii::ascii> &a0,
              const std::shared_ptr<Ascii::ascii> &a1,
              const std::shared_ptr<String::string> &a2) {
        return std::shared_ptr<Edit::edit>(new Edit::edit(update{a0, a1, a2}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct Chain {
  struct chain {
  public:
    struct empty {};
    struct skip {
      std::shared_ptr<Ascii::ascii> _a0;
      std::shared_ptr<String::string> _a1;
      std::shared_ptr<String::string> _a2;
      std::shared_ptr<Nat::nat> _a3;
      std::shared_ptr<Chain::chain> _a4;
    };
    struct change {
      std::shared_ptr<String::string> _a0;
      std::shared_ptr<String::string> _a1;
      std::shared_ptr<String::string> _a2;
      std::shared_ptr<Nat::nat> _a3;
      std::shared_ptr<Edit::edit> _a4;
      std::shared_ptr<Chain::chain> _a5;
    };
    using variant_t = std::variant<empty, skip, change>;

  private:
    variant_t v_;
    explicit chain(empty x) : v_(std::move(x)) {}
    explicit chain(skip x) : v_(std::move(x)) {}
    explicit chain(change x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Chain::chain> empty_() {
        return std::shared_ptr<Chain::chain>(new Chain::chain(empty{}));
      }
      static std::shared_ptr<Chain::chain>
      skip_(const std::shared_ptr<Ascii::ascii> &a0,
            const std::shared_ptr<String::string> &a1,
            const std::shared_ptr<String::string> &a2,
            const std::shared_ptr<Nat::nat> &a3,
            const std::shared_ptr<Chain::chain> &a4) {
        return std::shared_ptr<Chain::chain>(
            new Chain::chain(skip{a0, a1, a2, a3, a4}));
      }
      static std::shared_ptr<Chain::chain>
      change_(const std::shared_ptr<String::string> &a0,
              const std::shared_ptr<String::string> &a1,
              const std::shared_ptr<String::string> &a2,
              const std::shared_ptr<Nat::nat> &a3,
              const std::shared_ptr<Edit::edit> &a4,
              const std::shared_ptr<Chain::chain> &a5) {
        return std::shared_ptr<Chain::chain>(
            new Chain::chain(change{a0, a1, a2, a3, a4, a5}));
      }
    };
    const variant_t &v() const { return v_; }
    std::shared_ptr<Chain::chain>
    insert_chain(const std::shared_ptr<Ascii::ascii> &c,
                 const std::shared_ptr<String::string> &s1,
                 const std::shared_ptr<String::string> &s2,
                 const std::shared_ptr<Nat::nat> &n) const {
      return Chain::chain::ctor::change_(
          s1, String::string::ctor::String_(c, s1),
          String::string::ctor::String_(c, s2), n,
          Edit::edit::ctor::insertion_(c, s1),
          Chain::chain::ctor::skip_(c, s1, s2, n, this));
    }
    std::shared_ptr<Chain::chain>
    delete_chain(const std::shared_ptr<Ascii::ascii> &c,
                 const std::shared_ptr<String::string> &s1,
                 const std::shared_ptr<String::string> &s2,
                 const std::shared_ptr<Nat::nat> &n) const {
      return Chain::chain::ctor::change_(
          String::string::ctor::String_(c, s1), s1, s2, n,
          Edit::edit::ctor::deletion_(c, s1), this);
    }
    std::shared_ptr<Chain::chain>
    update_chain(const std::shared_ptr<Ascii::ascii> &c,
                 const std::shared_ptr<Ascii::ascii> &c_,
                 const std::shared_ptr<String::string> &s1,
                 const std::shared_ptr<String::string> &s2,
                 const std::shared_ptr<Nat::nat> &n) const {
      return Chain::chain::ctor::change_(
          String::string::ctor::String_(c, s1),
          String::string::ctor::String_(c_, s1),
          String::string::ctor::String_(c_, s2), n,
          Edit::edit::ctor::update_(c, c_, s1),
          Chain::chain::ctor::skip_(c_, s1, s2, n, this));
    }
    std::shared_ptr<Chain::chain>
    aux_insert(const std::shared_ptr<String::string> &_x,
               const std::shared_ptr<String::string> &_x0,
               const std::shared_ptr<Ascii::ascii> &x,
               const std::shared_ptr<String::string> &xs,
               const std::shared_ptr<Ascii::ascii> &y,
               const std::shared_ptr<String::string> &ys,
               const std::shared_ptr<Nat::nat> &n) const {
      return this->insert_chain(y, String::string::ctor::String_(x, xs), ys, n);
    }
    std::shared_ptr<Chain::chain>
    aux_delete(const std::shared_ptr<String::string> &_x,
               const std::shared_ptr<String::string> &_x0,
               const std::shared_ptr<Ascii::ascii> &x,
               const std::shared_ptr<String::string> &xs,
               const std::shared_ptr<Ascii::ascii> &y,
               const std::shared_ptr<String::string> &ys,
               const std::shared_ptr<Nat::nat> &n) const {
      return this->delete_chain(x, xs, String::string::ctor::String_(y, ys), n);
    }
    std::shared_ptr<Chain::chain>
    aux_update(const std::shared_ptr<String::string> &_x,
               const std::shared_ptr<String::string> &_x0,
               const std::shared_ptr<Ascii::ascii> &x,
               const std::shared_ptr<String::string> &xs,
               const std::shared_ptr<Ascii::ascii> &y,
               const std::shared_ptr<String::string> &ys,
               const std::shared_ptr<Nat::nat> &n) const {
      return this->update_chain(x, y, xs, ys, n);
    }
    std::shared_ptr<Chain::chain>
    aux_eq_char(const std::shared_ptr<String::string> &_x,
                const std::shared_ptr<String::string> &_x0,
                const std::shared_ptr<Ascii::ascii> &_x1,
                const std::shared_ptr<String::string> &xs,
                const std::shared_ptr<Ascii::ascii> &y,
                const std::shared_ptr<String::string> &ys,
                const std::shared_ptr<Nat::nat> &n) const {
      return Chain::chain::ctor::skip_(y, xs, ys, n, this);
    }
  };
};

std::shared_ptr<Chain::chain>
inserts_chain_empty(const std::shared_ptr<String::string> &s);

std::shared_ptr<Chain::chain>
deletes_chain_empty(const std::shared_ptr<String::string> &s);

std::shared_ptr<Chain::chain>
aux_both_empty(const std::shared_ptr<String::string> &_x,
               const std::shared_ptr<String::string> &_x0);

template <typename T1, MapsTo<std::shared_ptr<Nat::nat>, T1> F3>
T1 min3_app(const T1 x, const T1 y, const T1 z, F3 &&f) {
  std::shared_ptr<Nat::nat> n1 = f(x);
  std::shared_ptr<Nat::nat> n2 = f(y);
  std::shared_ptr<Nat::nat> n3 = f(z);
  return std::visit(
      Overloaded{
          [&](const typename Bool0::bool0::true0 _args) -> T1 {
            return std::visit(
                Overloaded{[&](const typename Bool0::bool0::true0 _args) -> T1 {
                             return x;
                           },
                           [&](const typename Bool0::bool0::false0 _args)
                               -> T1 { return z; }},
                leb(n1, n3)->v());
          },
          [&](const typename Bool0::bool0::false0 _args) -> T1 {
            return std::visit(
                Overloaded{[&](const typename Bool0::bool0::true0 _args) -> T1 {
                             return y;
                           },
                           [&](const typename Bool0::bool0::false0 _args)
                               -> T1 { return z; }},
                leb(n2, n3)->v());
          }},
      leb(n1, n2)->v());
}

std::shared_ptr<
    SigT::sigT<std::shared_ptr<Nat::nat>, std::shared_ptr<Chain::chain>>>
levenshtein_chain(const std::shared_ptr<String::string> &,
                  const std::shared_ptr<String::string> &);
