#ifndef INCLUDED_NO_MAPPING_EVENT_PROBE
#define INCLUDED_NO_MAPPING_EVENT_PROBE

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct NoMappingEventProbe {
  struct reproE {
    // TYPES
    struct Hidden {
      uint64_t a0;
      uint64_t a1;
    };

    struct Revealed {
      uint64_t a0;
      uint64_t a1;
    };

    using variant_t = std::variant<Hidden, Revealed>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    reproE() {}

    explicit reproE(Hidden _v) : v_(std::move(_v)) {}

    explicit reproE(Revealed _v) : v_(std::move(_v)) {}

    static reproE hidden(uint64_t a0, uint64_t a1) {
      return reproE(Hidden{a0, a1});
    }

    static reproE revealed(uint64_t a0, uint64_t a1) {
      return reproE(Revealed{a0, a1});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &>
  static T1 reproE_rect(F0 &&f, F1 &&f0, const reproE &r) {
    if (std::holds_alternative<typename reproE::Hidden>(r.v())) {
      const auto &[a0, a1] = std::get<typename reproE::Hidden>(r.v());
      return f(a0, a1);
    } else {
      const auto &[a0, a1] = std::get<typename reproE::Revealed>(r.v());
      return f0(a0, a1);
    }
  }

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &>
  static T1 reproE_rec(F0 &&f, F1 &&f0, const reproE &r) {
    if (std::holds_alternative<typename reproE::Hidden>(r.v())) {
      const auto &[a0, a1] = std::get<typename reproE::Hidden>(r.v());
      return f(a0, a1);
    } else {
      const auto &[a0, a1] = std::get<typename reproE::Revealed>(r.v());
      return f0(a0, a1);
    }
  }

  static inline const uint64_t cell_size = UINT64_C(42);
  static void draw_hidden_tile(uint64_t x, uint64_t y);
  static void draw_revealed_tile(uint64_t x, uint64_t y);
  static void loop(uint64_t x, uint64_t y, const List<bool> &cells);
};

#endif // INCLUDED_NO_MAPPING_EVENT_PROBE
