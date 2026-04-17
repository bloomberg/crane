#ifndef INCLUDED_NO_MAPPING_EVENT_PROBE
#define INCLUDED_NO_MAPPING_EVENT_PROBE

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

struct NoMappingEventProbe {
  struct reproE {
    // TYPES
    struct Hidden {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct Revealed {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    using variant_t = std::variant<Hidden, Revealed>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit reproE(Hidden _v) : d_v_(std::move(_v)) {}

    explicit reproE(Revealed _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<reproE> hidden(unsigned int a0, unsigned int a1) {
      return std::make_shared<reproE>(Hidden{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<reproE> revealed(unsigned int a0, unsigned int a1) {
      return std::make_shared<reproE>(Revealed{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int, unsigned int> F1>
  static T1 reproE_rect(F0 &&f, F1 &&f0, const std::shared_ptr<reproE> &r) {
    if (std::holds_alternative<typename reproE::Hidden>(r->v())) {
      const auto &[d_a0, d_a1] = std::get<typename reproE::Hidden>(r->v());
      return f(d_a0, d_a1);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename reproE::Revealed>(r->v());
      return f0(d_a0, d_a1);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int, unsigned int> F1>
  static T1 reproE_rec(F0 &&f, F1 &&f0, const std::shared_ptr<reproE> &r) {
    if (std::holds_alternative<typename reproE::Hidden>(r->v())) {
      const auto &[d_a0, d_a1] = std::get<typename reproE::Hidden>(r->v());
      return f(d_a0, d_a1);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename reproE::Revealed>(r->v());
      return f0(d_a0, d_a1);
    }
  }

  static inline const unsigned int cell_size = 42u;
  static void draw_hidden_tile(const unsigned int x, const unsigned int y);
  static void draw_revealed_tile(const unsigned int x, const unsigned int y);
  static void loop(const unsigned int x, const unsigned int y,
                   const std::shared_ptr<List<bool>> &cells);
};

#endif // INCLUDED_NO_MAPPING_EVENT_PROBE
