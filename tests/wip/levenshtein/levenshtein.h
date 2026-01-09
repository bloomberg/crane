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
  struct true0;
  struct false0;
  using bool0 = std::variant<true0, false0>;
  struct true0 {
    static std::shared_ptr<bool0> make();
  };
  struct false0 {
    static std::shared_ptr<bool0> make();
  };
};

struct Nat {
  struct O;
  struct S;
  using nat = std::variant<O, S>;
  struct O {
    static std::shared_ptr<nat> make();
  };
  struct S {
    std::shared_ptr<nat> _a0;
    static std::shared_ptr<nat> make(std::shared_ptr<nat> _a0);
  };
};

struct SigT {
  template <typename A, typename P> struct existT;
  template <typename A, typename P> using sigT = std::variant<existT<A, P>>;
  template <typename A, typename P> struct existT {
    A _a0;
    P _a1;
    static std::shared_ptr<sigT<A, P>> make(A _a0, P _a1) {
      return std::make_shared<sigT<A, P>>(existT<A, P>{_a0, _a1});
    }
  };
};

template <typename T1, typename T2>
T1 projT1(const std::shared_ptr<typename SigT::sigT<T1, T2>> x) {
  return std::visit(
      Overloaded{[&](const typename SigT::existT<T1, T2> _args) -> T1 {
        T1 a = _args._a0;
        return a;
      }},
      *x);
}

struct Sumbool {
  struct left;
  struct right;
  using sumbool = std::variant<left, right>;
  struct left {
    static std::shared_ptr<sumbool> make();
  };
  struct right {
    static std::shared_ptr<sumbool> make();
  };
};

std::shared_ptr<typename Bool0::bool0>
leb(const std::shared_ptr<typename Nat::nat> n,
    const std::shared_ptr<typename Nat::nat> m);

std::shared_ptr<typename Sumbool::sumbool>
bool_dec(const std::shared_ptr<typename Bool0::bool0> b1,
         const std::shared_ptr<typename Bool0::bool0> b2);

struct Ascii {
  struct Ascii;
  using ascii = std::variant<Ascii>;
  struct Ascii {
    std::shared_ptr<typename Bool0::bool0> _a0;
    std::shared_ptr<typename Bool0::bool0> _a1;
    std::shared_ptr<typename Bool0::bool0> _a2;
    std::shared_ptr<typename Bool0::bool0> _a3;
    std::shared_ptr<typename Bool0::bool0> _a4;
    std::shared_ptr<typename Bool0::bool0> _a5;
    std::shared_ptr<typename Bool0::bool0> _a6;
    std::shared_ptr<typename Bool0::bool0> _a7;
    static std::shared_ptr<ascii>
    make(std::shared_ptr<typename Bool0::bool0> _a0,
         std::shared_ptr<typename Bool0::bool0> _a1,
         std::shared_ptr<typename Bool0::bool0> _a2,
         std::shared_ptr<typename Bool0::bool0> _a3,
         std::shared_ptr<typename Bool0::bool0> _a4,
         std::shared_ptr<typename Bool0::bool0> _a5,
         std::shared_ptr<typename Bool0::bool0> _a6,
         std::shared_ptr<typename Bool0::bool0> _a7);
  };
};

std::shared_ptr<typename Sumbool::sumbool>
ascii_dec(const std::shared_ptr<typename Ascii::ascii> a,
          const std::shared_ptr<typename Ascii::ascii> b);

struct String {
  struct EmptyString;
  struct String;
  using string = std::variant<EmptyString, String>;
  struct EmptyString {
    static std::shared_ptr<string> make();
  };
  struct String {
    std::shared_ptr<typename Ascii::ascii> _a0;
    std::shared_ptr<string> _a1;
    static std::shared_ptr<string>
    make(std::shared_ptr<typename Ascii::ascii> _a0,
         std::shared_ptr<string> _a1);
  };
};

std::shared_ptr<typename Nat::nat>
length(const std::shared_ptr<typename String::string> s);

struct Edit {
  struct insertion;
  struct deletion;
  struct update;
  using edit = std::variant<insertion, deletion, update>;
  struct insertion {
    std::shared_ptr<typename Ascii::ascii> _a0;
    std::shared_ptr<typename String::string> _a1;
    static std::shared_ptr<edit>
    make(std::shared_ptr<typename Ascii::ascii> _a0,
         std::shared_ptr<typename String::string> _a1);
  };
  struct deletion {
    std::shared_ptr<typename Ascii::ascii> _a0;
    std::shared_ptr<typename String::string> _a1;
    static std::shared_ptr<edit>
    make(std::shared_ptr<typename Ascii::ascii> _a0,
         std::shared_ptr<typename String::string> _a1);
  };
  struct update {
    std::shared_ptr<typename Ascii::ascii> _a0;
    std::shared_ptr<typename Ascii::ascii> _a1;
    std::shared_ptr<typename String::string> _a2;
    static std::shared_ptr<edit>
    make(std::shared_ptr<typename Ascii::ascii> _a0,
         std::shared_ptr<typename Ascii::ascii> _a1,
         std::shared_ptr<typename String::string> _a2);
  };
};

struct Chain {
  struct empty;
  struct skip;
  struct change;
  using chain = std::variant<empty, skip, change>;
  struct empty {
    static std::shared_ptr<chain> make();
  };
  struct skip {
    std::shared_ptr<typename Ascii::ascii> _a0;
    std::shared_ptr<typename String::string> _a1;
    std::shared_ptr<typename String::string> _a2;
    std::shared_ptr<typename Nat::nat> _a3;
    std::shared_ptr<chain> _a4;
    static std::shared_ptr<chain>
    make(std::shared_ptr<typename Ascii::ascii> _a0,
         std::shared_ptr<typename String::string> _a1,
         std::shared_ptr<typename String::string> _a2,
         std::shared_ptr<typename Nat::nat> _a3, std::shared_ptr<chain> _a4);
  };
  struct change {
    std::shared_ptr<typename String::string> _a0;
    std::shared_ptr<typename String::string> _a1;
    std::shared_ptr<typename String::string> _a2;
    std::shared_ptr<typename Nat::nat> _a3;
    std::shared_ptr<typename Edit::edit> _a4;
    std::shared_ptr<chain> _a5;
    static std::shared_ptr<chain>
    make(std::shared_ptr<typename String::string> _a0,
         std::shared_ptr<typename String::string> _a1,
         std::shared_ptr<typename String::string> _a2,
         std::shared_ptr<typename Nat::nat> _a3,
         std::shared_ptr<typename Edit::edit> _a4, std::shared_ptr<chain> _a5);
  };
};

std::shared_ptr<typename Chain::chain>
insert_chain(const std::shared_ptr<typename Ascii::ascii> c,
             const std::shared_ptr<typename String::string> s1,
             const std::shared_ptr<typename String::string> s2,
             const std::shared_ptr<typename Nat::nat> n,
             const std::shared_ptr<typename Chain::chain> c0);

std::shared_ptr<typename Chain::chain>
inserts_chain_empty(const std::shared_ptr<typename String::string> s);

std::shared_ptr<typename Chain::chain>
delete_chain(const std::shared_ptr<typename Ascii::ascii> c,
             const std::shared_ptr<typename String::string> s1,
             const std::shared_ptr<typename String::string> s2,
             const std::shared_ptr<typename Nat::nat> n,
             const std::shared_ptr<typename Chain::chain> c0);

std::shared_ptr<typename Chain::chain>
deletes_chain_empty(const std::shared_ptr<typename String::string> s);

std::shared_ptr<typename Chain::chain>
update_chain(const std::shared_ptr<typename Ascii::ascii> c,
             const std::shared_ptr<typename Ascii::ascii> c_,
             const std::shared_ptr<typename String::string> s1,
             const std::shared_ptr<typename String::string> s2,
             const std::shared_ptr<typename Nat::nat> n,
             const std::shared_ptr<typename Chain::chain> c0);

std::shared_ptr<typename Chain::chain>
aux_insert(const std::shared_ptr<typename String::string> _x,
           const std::shared_ptr<typename String::string> _x0,
           const std::shared_ptr<typename Ascii::ascii> x,
           const std::shared_ptr<typename String::string> xs,
           const std::shared_ptr<typename Ascii::ascii> y,
           const std::shared_ptr<typename String::string> ys,
           const std::shared_ptr<typename Nat::nat> n,
           const std::shared_ptr<typename Chain::chain> r1);

std::shared_ptr<typename Chain::chain>
aux_delete(const std::shared_ptr<typename String::string> _x,
           const std::shared_ptr<typename String::string> _x0,
           const std::shared_ptr<typename Ascii::ascii> x,
           const std::shared_ptr<typename String::string> xs,
           const std::shared_ptr<typename Ascii::ascii> y,
           const std::shared_ptr<typename String::string> ys,
           const std::shared_ptr<typename Nat::nat> n,
           const std::shared_ptr<typename Chain::chain> r2);

std::shared_ptr<typename Chain::chain>
aux_update(const std::shared_ptr<typename String::string> _x,
           const std::shared_ptr<typename String::string> _x0,
           const std::shared_ptr<typename Ascii::ascii> x,
           const std::shared_ptr<typename String::string> xs,
           const std::shared_ptr<typename Ascii::ascii> y,
           const std::shared_ptr<typename String::string> ys,
           const std::shared_ptr<typename Nat::nat> n,
           const std::shared_ptr<typename Chain::chain> r3);

std::shared_ptr<typename Chain::chain>
aux_eq_char(const std::shared_ptr<typename String::string> _x,
            const std::shared_ptr<typename String::string> _x0,
            const std::shared_ptr<typename Ascii::ascii> _x1,
            const std::shared_ptr<typename String::string> xs,
            const std::shared_ptr<typename Ascii::ascii> y,
            const std::shared_ptr<typename String::string> ys,
            const std::shared_ptr<typename Nat::nat> n,
            const std::shared_ptr<typename Chain::chain> c);

std::shared_ptr<typename Chain::chain>
aux_both_empty(const std::shared_ptr<typename String::string> _x,
               const std::shared_ptr<typename String::string> _x0);

template <typename T1, MapsTo<std::shared_ptr<typename Nat::nat>, T1> F3>
T1 min3_app(const T1 x, const T1 y, const T1 z, F3 &&f) {
  std::shared_ptr<typename Nat::nat> n1 = f(x);
  std::shared_ptr<typename Nat::nat> n2 = f(y);
  std::shared_ptr<typename Nat::nat> n3 = f(z);
  return std::visit(
      Overloaded{
          [&](const typename Bool0::true0 _args) -> T1 {
            return std::visit(
                Overloaded{
                    [&](const typename Bool0::true0 _args) -> T1 { return x; },
                    [&](const typename Bool0::false0 _args) -> T1 {
                      return z;
                    }},
                *leb(n1, n3));
          },
          [&](const typename Bool0::false0 _args) -> T1 {
            return std::visit(
                Overloaded{
                    [&](const typename Bool0::true0 _args) -> T1 { return y; },
                    [&](const typename Bool0::false0 _args) -> T1 {
                      return z;
                    }},
                *leb(n2, n3));
          }},
      *leb(n1, n2));
}

std::shared_ptr<typename SigT::sigT<std::shared_ptr<typename Nat::nat>,
                                    std::shared_ptr<typename Chain::chain>>>
levenshtein_chain(const std::shared_ptr<typename String::string>,
                  const std::shared_ptr<typename String::string>);
