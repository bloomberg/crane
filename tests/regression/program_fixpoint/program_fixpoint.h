#ifndef INCLUDED_PROGRAM_FIXPOINT
#define INCLUDED_PROGRAM_FIXPOINT

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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Sig<t_A>> exist(t_A x) {
    return std::make_shared<Sig<t_A>>(Exist{std::move(x)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
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
    const auto &[d_x, d_a1] =
        std::get<typename SigT<t_A, t_P>::ExistT>(this->v());
    return d_x;
  }

  t_P projT2() const {
    const auto &[d_x, d_a1] =
        std::get<typename SigT<t_A, t_P>::ExistT>(this->v());
    return d_a1;
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
      interleave(List<unsigned int>::cons(
                     1u, List<unsigned int>::cons(
                             3u, List<unsigned int>::cons(
                                     5u, List<unsigned int>::nil()))),
                 List<unsigned int>::cons(
                     2u, List<unsigned int>::cons(
                             4u, List<unsigned int>::cons(
                                     6u, List<unsigned int>::nil()))));
};

#endif // INCLUDED_PROGRAM_FIXPOINT
