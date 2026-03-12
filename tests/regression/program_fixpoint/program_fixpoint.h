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
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
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

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct Sig {
  // TYPES
  struct exist {
    A _a0;
  };

  using variant_t = std::variant<exist>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit Sig(exist _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Sig<A>> exist_(A a0) {
      return std::shared_ptr<Sig<A>>(new Sig<A>(exist{a0}));
    }

    static std::unique_ptr<Sig<A>> exist_uptr(A a0) {
      return std::unique_ptr<Sig<A>>(new Sig<A>(exist{a0}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
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

  P projT2() const {
    return std::visit(
        Overloaded{[](const typename SigT<A, P>::existT _args) -> P {
          P h = _args._a1;
          return h;
        }},
        this->v());
  }
};

struct ProgFix {
  static std::shared_ptr<List<unsigned int>> interleave_func(
      const std::shared_ptr<SigT<std::shared_ptr<List<unsigned int>>,
                                 std::shared_ptr<List<unsigned int>>>> &x);
  static std::shared_ptr<List<unsigned int>>
  interleave(std::shared_ptr<List<unsigned int>> l1,
             std::shared_ptr<List<unsigned int>> l2);
  static inline const std::shared_ptr<List<unsigned int>> test_interleave =
      interleave(List<unsigned int>::ctor::cons_(
                     1u, List<unsigned int>::ctor::cons_(
                             3u, List<unsigned int>::ctor::cons_(
                                     5u, List<unsigned int>::ctor::nil_()))),
                 List<unsigned int>::ctor::cons_(
                     2u, List<unsigned int>::ctor::cons_(
                             4u, List<unsigned int>::ctor::cons_(
                                     6u, List<unsigned int>::ctor::nil_()))));
};
