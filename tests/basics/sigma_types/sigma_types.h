#ifndef INCLUDED_SIGMA_TYPES
#define INCLUDED_SIGMA_TYPES

#include <any>
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
    const auto &_m = *std::get_if<typename SigT<t_A, t_P>::ExistT>(&this->v());
    return _m.d_x;
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
  static inline const unsigned int test_double_pos = []() {
    auto &&_sv0 = double_positive(3u);
    const auto &_m0 =
        *std::get_if<typename Sig<unsigned int>::Exist>(&_sv0->v());
    return _m0.d_x;
  }();
  static inline const std::shared_ptr<List<unsigned int>> test_positives =
      positives_up_to(5u);
};

#endif // INCLUDED_SIGMA_TYPES
