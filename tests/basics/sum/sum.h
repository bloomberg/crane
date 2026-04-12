#ifndef INCLUDED_SUM
#define INCLUDED_SUM

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

struct Sum {
  template <typename t_A, typename t_B> struct either {
    // TYPES
    struct Left {
      t_A d_a0;
    };

    struct Right {
      t_B d_a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit either(Left _v) : d_v_(std::move(_v)) {}

    explicit either(Right _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<either<t_A, t_B>> left(t_A a0) {
      return std::make_shared<either<t_A, t_B>>(Left{std::move(a0)});
    }

    static std::shared_ptr<either<t_A, t_B>> right(t_B a0) {
      return std::make_shared<either<t_A, t_B>>(Right{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_B> F0>
    std::shared_ptr<either<t_A, T1>> map_right(F0 &&f) const {
      return std::visit(
          Overloaded{[](const typename either<t_A, t_B>::Left &_args)
                         -> std::shared_ptr<either<t_A, T1>> {
                       return either<t_A, T1>::left(_args.d_a0);
                     },
                     [&](const typename either<t_A, t_B>::Right &_args)
                         -> std::shared_ptr<either<t_A, T1>> {
                       return either<t_A, T1>::right(f(_args.d_a0));
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0>
    std::shared_ptr<either<T1, t_B>> map_left(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename either<t_A, t_B>::Left &_args)
                         -> std::shared_ptr<either<T1, t_B>> {
                       return either<T1, t_B>::left(f(_args.d_a0));
                     },
                     [](const typename either<t_A, t_B>::Right &_args)
                         -> std::shared_ptr<either<T1, t_B>> {
                       return either<T1, t_B>::right(_args.d_a0);
                     }},
          this->v());
    }

    __attribute__((pure)) bool is_left() const {
      return std::visit(
          Overloaded{[](const typename either<t_A, t_B>::Left &) -> bool {
                       return true;
                     },
                     [](const typename either<t_A, t_B>::Right &) -> bool {
                       return false;
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1>
    T1 either_rec(F0 &&f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename either<t_A, t_B>::Left &_args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename either<t_A, t_B>::Right &_args) -> T1 {
                       return f0(_args.d_a0);
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1>
    T1 either_rect(F0 &&f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename either<t_A, t_B>::Left &_args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename either<t_A, t_B>::Right &_args) -> T1 {
                       return f0(_args.d_a0);
                     }},
          this->v());
    }
  };

  static inline const std::shared_ptr<either<unsigned int, bool>> left_val =
      either<unsigned int, bool>::left(5u);
  static inline const std::shared_ptr<either<unsigned int, bool>> right_val =
      either<unsigned int, bool>::right(true);
  __attribute__((pure)) static unsigned int
  either_to_nat(const std::shared_ptr<either<unsigned int, unsigned int>> &e);

  template <typename t_A, typename t_B, typename t_C> struct triple {
    // TYPES
    struct First {
      t_A d_a0;
    };

    struct Second {
      t_B d_a0;
    };

    struct Third {
      t_C d_a0;
    };

    using variant_t = std::variant<First, Second, Third>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit triple(First _v) : d_v_(std::move(_v)) {}

    explicit triple(Second _v) : d_v_(std::move(_v)) {}

    explicit triple(Third _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<triple<t_A, t_B, t_C>> first(t_A a0) {
      return std::make_shared<triple<t_A, t_B, t_C>>(First{std::move(a0)});
    }

    static std::shared_ptr<triple<t_A, t_B, t_C>> second(t_B a0) {
      return std::make_shared<triple<t_A, t_B, t_C>>(Second{std::move(a0)});
    }

    static std::shared_ptr<triple<t_A, t_B, t_C>> third(t_C a0) {
      return std::make_shared<triple<t_A, t_B, t_C>>(Third{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1,
              MapsTo<T1, t_C> F2>
    T1 triple_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return std::visit(
          Overloaded{
              [&](const typename triple<t_A, t_B, t_C>::First &_args) -> T1 {
                return f(_args.d_a0);
              },
              [&](const typename triple<t_A, t_B, t_C>::Second &_args) -> T1 {
                return f0(_args.d_a0);
              },
              [&](const typename triple<t_A, t_B, t_C>::Third &_args) -> T1 {
                return f1(_args.d_a0);
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1,
              MapsTo<T1, t_C> F2>
    T1 triple_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      return std::visit(
          Overloaded{
              [&](const typename triple<t_A, t_B, t_C>::First &_args) -> T1 {
                return f(_args.d_a0);
              },
              [&](const typename triple<t_A, t_B, t_C>::Second &_args) -> T1 {
                return f0(_args.d_a0);
              },
              [&](const typename triple<t_A, t_B, t_C>::Third &_args) -> T1 {
                return f1(_args.d_a0);
              }},
          this->v());
    }
  };

  static inline const std::shared_ptr<triple<unsigned int, bool, unsigned int>>
      triple_test = triple<unsigned int, bool, unsigned int>::second(true);
  static inline const bool test_left = left_val->is_left();
  static inline const bool test_right = right_val->is_left();
  static inline const unsigned int test_either =
      either_to_nat(either<unsigned int, unsigned int>::left(3u));
};

#endif // INCLUDED_SUM
