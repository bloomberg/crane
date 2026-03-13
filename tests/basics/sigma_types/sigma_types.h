#ifndef INCLUDED_SIGMA_TYPES
#define INCLUDED_SIGMA_TYPES

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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_a0;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Sig<t_A>> Exist_(t_A a0) {
      return std::shared_ptr<Sig<t_A>>(new Sig<t_A>(Exist{a0}));
    }

    static std::unique_ptr<Sig<t_A>> Exist_uptr(t_A a0) {
      return std::unique_ptr<Sig<t_A>>(new Sig<t_A>(Exist{a0}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
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

struct SigmaTypes {
  static std::shared_ptr<SigT<unsigned int, std::any>>
  nat_with_double(const unsigned int n);
  static std::shared_ptr<Sig<unsigned int>> positive_succ(const unsigned int n);
  __attribute__((pure)) static unsigned int get_positive(const unsigned int n);
  static std::shared_ptr<Sig<unsigned int>>
  double_positive(const unsigned int n);
  __attribute__((pure)) static unsigned int
  use_nat_double(const unsigned int n);
  static std::shared_ptr<List<unsigned int>>
  positives_up_to(const unsigned int k);
  static inline const unsigned int test_double_5 = use_nat_double(5u);
  static inline const unsigned int test_positive_3 = get_positive(3u);
  static inline const unsigned int test_double_pos = std::visit(
      Overloaded{[](const typename Sig<unsigned int>::Exist _args) -> auto {
        auto a = _args.d_a0;
        return a;
      }},
      double_positive(3u)->v());
  static inline const std::shared_ptr<List<unsigned int>> test_positives =
      positives_up_to(5u);
};

#endif // INCLUDED_SIGMA_TYPES
