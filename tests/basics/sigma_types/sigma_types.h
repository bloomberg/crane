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

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

template <typename A> struct Sig {
public:
  struct exist {
    A _a0;
  };
  using variant_t = std::variant<exist>;

private:
  variant_t v_;
  explicit Sig(exist _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<Sig<A>> exist_(A a0) {
      return std::shared_ptr<Sig<A>>(new Sig<A>(exist{a0}));
    }
    static std::unique_ptr<Sig<A>> exist_uptr(A a0) {
      return std::unique_ptr<Sig<A>>(new Sig<A>(exist{a0}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

template <typename A, typename P> struct SigT {
public:
  struct existT {
    A _a0;
    P _a1;
  };
  using variant_t = std::variant<existT>;

private:
  variant_t v_;
  explicit SigT(existT _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<SigT<A, P>> existT_(A a0, P a1) {
      return std::shared_ptr<SigT<A, P>>(new SigT<A, P>(existT{a0, a1}));
    }
    static std::unique_ptr<SigT<A, P>> existT_uptr(A a0, P a1) {
      return std::unique_ptr<SigT<A, P>>(new SigT<A, P>(existT{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
  A projT1() const {
    return std::visit(
        Overloaded{[](const typename SigT<A, P>::existT _args) -> A {
          A a = _args._a0;
          return a;
        }},
        this->v());
  }
};

struct SigmaTypes {
  static std::shared_ptr<SigT<unsigned int, std::any>>
  nat_with_double(const unsigned int n);

  static std::shared_ptr<Sig<unsigned int>> positive_succ(const unsigned int n);

  static unsigned int get_positive(const unsigned int n);

  static std::shared_ptr<Sig<unsigned int>>
  double_positive(const unsigned int n);

  static unsigned int use_nat_double(const unsigned int n);

  static std::shared_ptr<List<unsigned int>>
  positives_up_to(const unsigned int k);

  static inline const unsigned int test_double_5 =
      use_nat_double((((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_positive_3 =
      get_positive((((0 + 1) + 1) + 1));

  static inline const unsigned int test_double_pos = std::visit(
      Overloaded{[](const typename Sig<unsigned int>::exist _args) -> auto {
        auto a = _args._a0;
        return a;
      }},
      double_positive((((0 + 1) + 1) + 1))->v());

  static inline const std::shared_ptr<List<unsigned int>> test_positives =
      positives_up_to((((((0 + 1) + 1) + 1) + 1) + 1));
};
