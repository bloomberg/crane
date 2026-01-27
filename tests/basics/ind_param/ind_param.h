#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename M>
concept Container = requires {
  typename M::elem;
  {
    M::t_rect(std::declval<T1>(), std::declval<std::function<T1(elem)>>(),
              std::declval<std::function<T1(elem, elem)>>(),
              std::declval<std::shared_ptr<T::t>>())
  } -> std::same_as<T1>;
  {
    M::t_rec(std::declval<T1>(), std::declval<std::function<T1(elem)>>(),
             std::declval<std::function<T1(elem, elem)>>(),
             std::declval<std::shared_ptr<T::t>>())
  } -> std::same_as<T1>;
  {
    M::size(std::declval<std::shared_ptr<T::t>>())
  } -> std::same_as<unsigned int>;
};

template <Container C> struct Wrapper {
  using wrapped = std::shared_ptr<C::t>;

  struct result {
  public:
    struct Ok {
      std::shared_ptr<C::t> _a0;
    };
    struct Err {
      unsigned int _a0;
    };
    using variant_t = std::variant<Ok, Err>;

  private:
    variant_t v_;
    explicit result(Ok x) : v_(std::move(x)) {}
    explicit result(Err x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<result> Ok_(const std::shared_ptr<C::t> &a0) {
        return std::shared_ptr<result>(new result(Ok{a0}));
      }
      static std::shared_ptr<result> Err_(unsigned int a0) {
        return std::shared_ptr<result>(new result(Err{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<C::t>> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 result_rect(F0 &&f, F1 &&f0, const std::shared_ptr<result> &r) {
    return std::visit(Overloaded{[&](const typename result::Ok _args) -> T1 {
                                   std::shared_ptr<C::t> t0 = _args._a0;
                                   return f(t0);
                                 },
                                 [&](const typename result::Err _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f0(n);
                                 }},
                      r->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<C::t>> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 result_rec(F0 &&f, F1 &&f0, const std::shared_ptr<result> &r) {
    return std::visit(Overloaded{[&](const typename result::Ok _args) -> T1 {
                                   std::shared_ptr<C::t> t0 = _args._a0;
                                   return f(t0);
                                 },
                                 [&](const typename result::Err _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f0(n);
                                 }},
                      r->v());
  }

  static std::shared_ptr<result> make_single(const typename C::elem e) {
    return result::ctor::Ok_(c::t::ctor::Single_(e));
  }

  static std::shared_ptr<result> make_pair(const typename C::elem e1,
                                           const typename C::elem e2) {
    return result::ctor::Ok_(c::t::ctor::Pair_(e1, e2));
  }

  static unsigned int get_size(const std::shared_ptr<result> &r) {
    return std::visit(
        Overloaded{[&](const typename result::Ok _args) -> unsigned int {
                     std::shared_ptr<C::t> c = _args._a0;
                     return C::size(c);
                   },
                   [&](const typename result::Err _args) -> unsigned int {
                     return 0;
                   }},
        r->v());
  }

  static inline std::shared_ptr<result> empty_result =
      result::ctor::Ok_(c::t::ctor::Empty_());

 static inline std::shared_ptr<result> error_result = result::ctor::Err_(((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
};

struct NatContainer {
  using elem = unsigned int;

  struct t {
  public:
    struct Empty {};
    struct Single {
      elem _a0;
    };
    struct Pair {
      elem _a0;
      elem _a1;
    };
    using variant_t = std::variant<Empty, Single, Pair>;

  private:
    variant_t v_;
    explicit t(Empty x) : v_(std::move(x)) {}
    explicit t(Single x) : v_(std::move(x)) {}
    explicit t(Pair x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<t> Empty_() {
        return std::shared_ptr<t>(new t(Empty{}));
      }
      static std::shared_ptr<t> Single_(elem a0) {
        return std::shared_ptr<t>(new t(Single{a0}));
      }
      static std::shared_ptr<t> Pair_(elem a0, elem a1) {
        return std::shared_ptr<t>(new t(Pair{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int> F2>
  static T1 t_rect(const T1 f, F1 &&f0, F2 &&f1, const std::shared_ptr<t> &t0) {
    return std::visit(
        Overloaded{[&](const typename t::Empty _args) -> T1 { return f; },
                   [&](const typename t::Single _args) -> T1 {
                     unsigned int e = _args._a0;
                     return f0(e);
                   },
                   [&](const typename t::Pair _args) -> T1 {
                     unsigned int e = _args._a0;
                     unsigned int e0 = _args._a1;
                     return f1(e, e0);
                   }},
        t0->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1,
            MapsTo<T1, unsigned int, unsigned int> F2>
  static T1 t_rec(const T1 f, F1 &&f0, F2 &&f1, const std::shared_ptr<t> &t0) {
    return std::visit(
        Overloaded{[&](const typename t::Empty _args) -> T1 { return f; },
                   [&](const typename t::Single _args) -> T1 {
                     unsigned int e = _args._a0;
                     return f0(e);
                   },
                   [&](const typename t::Pair _args) -> T1 {
                     unsigned int e = _args._a0;
                     unsigned int e0 = _args._a1;
                     return f1(e, e0);
                   }},
        t0->v());
  }

  static unsigned int size(const std::shared_ptr<t> &c);
};

using NatWrapper = Wrapper<NatContainer>;

const std::shared_ptr<NatWrapper::result> test_single = NatWrapper::make_single(
    ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1) +
       1) +
      1) +
     1));

const std::shared_ptr<NatWrapper::result> test_pair =
    NatWrapper::make_pair((0 + 1), ((0 + 1) + 1));

const unsigned int test_size_single = NatWrapper::get_size(test_single);

const unsigned int test_size_pair = NatWrapper::get_size(test_pair);

const unsigned int test_error = NatWrapper::get_size(NatWrapper::error_result);
