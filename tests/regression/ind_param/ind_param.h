#ifndef INCLUDED_IND_PARAM
#define INCLUDED_IND_PARAM

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

template <typename M>
concept Container = requires {
  typename M::elem;
  typename M::t;
  {
    M::size(std::declval<std::shared_ptr<typename M::t>>())
  } -> std::same_as<unsigned int>;
};

struct IndParam {
  template <Container C> struct Wrapper {
    using wrapped = std::shared_ptr<typename C::t>;

    struct result {
      // TYPES
      struct Ok {
        std::shared_ptr<typename C::t> d_a0;
      };

      struct Err {
        unsigned int d_a0;
      };

      using variant_t = std::variant<Ok, Err>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      explicit result(Ok _v) : d_v_(std::move(_v)) {}

      explicit result(Err _v) : d_v_(std::move(_v)) {}

      static std::shared_ptr<result>
      ok(const std::shared_ptr<typename C::t> &a0) {
        return std::make_shared<result>(Ok{a0});
      }

      static std::shared_ptr<result> ok(std::shared_ptr<typename C::t> &&a0) {
        return std::make_shared<result>(Ok{std::move(a0)});
      }

      static std::shared_ptr<result> err(unsigned int a0) {
        return std::make_shared<result>(Err{std::move(a0)});
      }

      // MANIPULATORS
      __attribute__((pure)) variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      __attribute__((pure)) const variant_t &v() const { return d_v_; }
    };

    template <typename T1, MapsTo<T1, std::shared_ptr<typename C::t>> F0,
              MapsTo<T1, unsigned int> F1>
    static T1 result_rect(F0 &&f, F1 &&f0, const std::shared_ptr<result> &r) {
      return std::visit(Overloaded{[&](const typename result::Ok _args) -> T1 {
                                     return f(_args.d_a0);
                                   },
                                   [&](const typename result::Err _args) -> T1 {
                                     return f0(_args.d_a0);
                                   }},
                        r->v());
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<typename C::t>> F0,
              MapsTo<T1, unsigned int> F1>
    static T1 result_rec(F0 &&f, F1 &&f0, const std::shared_ptr<result> &r) {
      return std::visit(Overloaded{[&](const typename result::Ok _args) -> T1 {
                                     return f(_args.d_a0);
                                   },
                                   [&](const typename result::Err _args) -> T1 {
                                     return f0(_args.d_a0);
                                   }},
                        r->v());
    }

    static std::shared_ptr<result> make_single(const typename C::elem e) {
      return result::ok(C::t::single(e));
    }

    static std::shared_ptr<result> make_pair(const typename C::elem e1,
                                             const typename C::elem e2) {
      return result::ok(C::t::pair(e1, e2));
    }

    __attribute__((pure)) static unsigned int
    get_size(const std::shared_ptr<result> &r) {
      return std::visit(
          Overloaded{
              [](const typename result::Ok _args) -> unsigned int {
                return C::size(_args.d_a0);
              },
              [](const typename result::Err) -> unsigned int { return 0u; }},
          r->v());
    }

    static const std::shared_ptr<result> &empty_result() {
      static const std::shared_ptr<result> v = result::ok(C::t::empty());
      return v;
    }

    static const std::shared_ptr<result> &error_result() {
      static const std::shared_ptr<result> v = result::err(404u);
      return v;
    }
  };

  struct NatContainer {
    using elem = unsigned int;

    struct t {
      // TYPES
      struct Empty {};

      struct Single {
        elem d_a0;
      };

      struct Pair {
        elem d_a0;
        elem d_a1;
      };

      using variant_t = std::variant<Empty, Single, Pair>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      explicit t(Empty _v) : d_v_(std::move(_v)) {}

      explicit t(Single _v) : d_v_(std::move(_v)) {}

      explicit t(Pair _v) : d_v_(std::move(_v)) {}

      static std::shared_ptr<t> empty() { return std::make_shared<t>(Empty{}); }

      static std::shared_ptr<t> single(elem a0) {
        return std::make_shared<t>(Single{std::move(a0)});
      }

      static std::shared_ptr<t> pair(elem a0, elem a1) {
        return std::make_shared<t>(Pair{std::move(a0), std::move(a1)});
      }

      // MANIPULATORS
      __attribute__((pure)) variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      __attribute__((pure)) const variant_t &v() const { return d_v_; }
    };

    template <typename T1, MapsTo<T1, unsigned int> F1,
              MapsTo<T1, unsigned int, unsigned int> F2>
    static T1 t_rect(const T1 f, F1 &&f0, F2 &&f1,
                     const std::shared_ptr<t> &t0) {
      return std::visit(
          Overloaded{[&](const typename t::Empty) -> T1 { return f; },
                     [&](const typename t::Single _args) -> T1 {
                       return f0(_args.d_a0);
                     },
                     [&](const typename t::Pair _args) -> T1 {
                       return f1(_args.d_a0, _args.d_a1);
                     }},
          t0->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F1,
              MapsTo<T1, unsigned int, unsigned int> F2>
    static T1 t_rec(const T1 f, F1 &&f0, F2 &&f1,
                    const std::shared_ptr<t> &t0) {
      return std::visit(
          Overloaded{[&](const typename t::Empty) -> T1 { return f; },
                     [&](const typename t::Single _args) -> T1 {
                       return f0(_args.d_a0);
                     },
                     [&](const typename t::Pair _args) -> T1 {
                       return f1(_args.d_a0, _args.d_a1);
                     }},
          t0->v());
    }

    __attribute__((pure)) static unsigned int size(const std::shared_ptr<t> &c);
  };

  using NatWrapper = Wrapper<NatContainer>;
  static inline const std::shared_ptr<NatWrapper::result> test_single =
      NatWrapper::make_single(42u);
  static inline const std::shared_ptr<NatWrapper::result> test_pair =
      NatWrapper::make_pair(1u, 2u);
  static inline const unsigned int test_size_single =
      NatWrapper::get_size(test_single);
  static inline const unsigned int test_size_pair =
      NatWrapper::get_size(test_pair);
  static inline const unsigned int test_error =
      NatWrapper::get_size(NatWrapper::error_result());
};

#endif // INCLUDED_IND_PARAM
