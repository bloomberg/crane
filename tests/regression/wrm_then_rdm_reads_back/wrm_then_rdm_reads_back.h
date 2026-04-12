#ifndef INCLUDED_WRM_THEN_RDM_READS_BACK
#define INCLUDED_WRM_THEN_RDM_READS_BACK

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

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      return std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil &) -> t_A { return default0; },
              [](const typename List<t_A>::Cons &_args) -> t_A {
                return _args.d_a0;
              }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil &) -> t_A { return default0; },
              [&](const typename List<t_A>::Cons &_args0) -> t_A {
                return _args0.d_a1->nth(m, default0);
              }},
          this->v());
    }
  }
};

struct WrmThenRdmReadsBack {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      return std::visit(
          Overloaded{
              [](const typename List<T1>::Nil &) -> std::shared_ptr<List<T1>> {
                return List<T1>::nil();
              },
              [&](const typename List<T1>::Cons &_args)
                  -> std::shared_ptr<List<T1>> {
                return List<T1>::cons(x, _args.d_a1);
              }},
          l->v());
    } else {
      unsigned int n_ = n - 1;
      return std::visit(
          Overloaded{
              [](const typename List<T1>::Nil &) -> std::shared_ptr<List<T1>> {
                return List<T1>::nil();
              },
              [&](const typename List<T1>::Cons &_args0)
                  -> std::shared_ptr<List<T1>> {
                return List<T1>::cons(_args0.d_a0,
                                      update_nth<T1>(n_, x, _args0.d_a1));
              }},
          l->v());
    }
  }

  struct state {
    std::shared_ptr<List<unsigned int>> regs;
    unsigned int acc;
    std::shared_ptr<List<unsigned int>> ram;
    unsigned int sel_char;
  };

  __attribute__((pure)) static unsigned int
  get_reg(const std::shared_ptr<state> &s, const unsigned int r);
  __attribute__((pure)) static unsigned int
  get_reg_pair(const std::shared_ptr<state> &s, const unsigned int r);
  static std::shared_ptr<state> execute_src(const std::shared_ptr<state> &s,
                                            const unsigned int r);
  static std::shared_ptr<state> execute_wrm(const std::shared_ptr<state> &s);
  static std::shared_ptr<state> execute_rdm(const std::shared_ptr<state> &s);
  static inline const std::shared_ptr<state> sample = std::make_shared<state>(
      state{List<unsigned int>::cons(
                0u,
                List<unsigned int>::cons(
                    0u,
                    List<unsigned int>::cons(
                        1u,
                        List<unsigned int>::cons(
                            3u, List<unsigned int>::cons(
                                    0u, List<unsigned int>::cons(
                                            0u, List<unsigned int>::nil())))))),
            12u,
            List<unsigned int>::cons(
                0u,
                List<unsigned int>::cons(
                    0u, List<unsigned int>::cons(
                            0u, List<unsigned int>::cons(
                                    5u, List<unsigned int>::cons(
                                            0u, List<unsigned int>::nil()))))),
            0u});
  static inline const std::shared_ptr<state> roundtrip =
      execute_rdm(execute_wrm(execute_src(sample, 3u)));
  static inline const bool t = roundtrip->acc == 12u;
};

#endif // INCLUDED_WRM_THEN_RDM_READS_BACK
