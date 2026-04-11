#ifndef INCLUDED_EMPTY_MATCH
#define INCLUDED_EMPTY_MATCH

#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct EmptyMatch {
  struct empty {
    empty() = delete;
  };

  template <typename T1> static T1 empty_rect(const std::shared_ptr<empty> &) {
    throw std::logic_error("absurd case");
  }

  template <typename T1> static T1 empty_rec(const std::shared_ptr<empty> &) {
    throw std::logic_error("absurd case");
  }

  template <typename T1> static T1 absurd(const std::shared_ptr<empty> &) {
    throw std::logic_error("absurd case");
  }

  __attribute__((pure)) static unsigned int
  from_empty(const std::shared_ptr<empty> &_x0);

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
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1> F0,
            MapsTo<T3, T2> F1>
  static T3 either_rect(F0 &&f, F1 &&f0,
                        const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(
        Overloaded{[&](const typename either<T1, T2>::Left _args) -> T3 {
                     return f(_args.d_a0);
                   },
                   [&](const typename either<T1, T2>::Right _args) -> T3 {
                     return f0(_args.d_a0);
                   }},
        e->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1> F0,
            MapsTo<T3, T2> F1>
  static T3 either_rec(F0 &&f, F1 &&f0,
                       const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(
        Overloaded{[&](const typename either<T1, T2>::Left _args) -> T3 {
                     return f(_args.d_a0);
                   },
                   [&](const typename either<T1, T2>::Right _args) -> T3 {
                     return f0(_args.d_a0);
                   }},
        e->v());
  }

  template <typename T1>
  static T1
  handle_left(const std::shared_ptr<either<T1, std::shared_ptr<empty>>> &e) {
    return std::visit(
        Overloaded{
            [](const typename either<T1, std::shared_ptr<empty>>::Left _args)
                -> T1 { return _args.d_a0; },
            [](const typename either<T1, std::shared_ptr<empty>>::Right _args)
                -> T1 { return absurd<T1>(_args.d_a0); }},
        e->v());
  }

  static inline const std::shared_ptr<
      either<unsigned int, std::shared_ptr<empty>>>
      test_either = either<unsigned int, std::shared_ptr<empty>>::left(5u);
  static inline const unsigned int test_handle =
      handle_left<unsigned int>(test_either);

  template <typename T1, typename T2>
  static std::shared_ptr<either<T1, T2>>
  complex_absurd(const std::shared_ptr<empty> &) {
    throw std::logic_error("absurd case");
  }
};

#endif // INCLUDED_EMPTY_MATCH
