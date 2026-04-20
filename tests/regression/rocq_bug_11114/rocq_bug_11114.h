#ifndef INCLUDED_ROCQ_BUG_11114
#define INCLUDED_ROCQ_BUG_11114

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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

struct RocqBug11114 {
  struct t {
    // TYPES
    struct T0 {
      unsigned int d_k;
    };

    using variant_t = std::variant<T0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit t(T0 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<t> t0(unsigned int k) {
      return std::make_shared<t>(T0{std::move(k)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 t_rect(const std::shared_ptr<List<unsigned int>> &, F1 &&f,
                   const std::shared_ptr<t> &t0) {
    const auto &[d_k] = std::get<typename t::T0>(t0->v());
    return f(d_k);
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 t_rec(const std::shared_ptr<List<unsigned int>> &, F1 &&f,
                  const std::shared_ptr<t> &t0) {
    const auto &[d_k] = std::get<typename t::T0>(t0->v());
    return f(d_k);
  }

  struct pkg {
    std::shared_ptr<List<unsigned int>> _sig;
    std::shared_ptr<t> _t;
  };

  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<pkg> map(F0 &&f, const std::shared_ptr<pkg> &p) {
    return std::make_shared<pkg>(pkg{p->_sig, [&]() {
                                       auto &&_sv = p->_t;
                                       const auto &[d_k] =
                                           std::get<typename t::T0>(_sv->v());
                                       return t::t0(f(d_k));
                                     }()});
  }

  static inline const std::shared_ptr<pkg> test_pkg = std::make_shared<pkg>(
      pkg{List<unsigned int>::cons(1u, List<unsigned int>::nil()), t::t0(2u)});
  static inline const std::shared_ptr<pkg> test_map =
      map([](const unsigned int x) { return (x + 1u); }, test_pkg);
};

#endif // INCLUDED_ROCQ_BUG_11114
