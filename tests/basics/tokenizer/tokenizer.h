#ifndef INCLUDED_TOKENIZER
#define INCLUDED_TOKENIZER

#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;
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

  std::shared_ptr<List<t_A>> rev() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return d_a1->rev()->app(List<t_A>::cons(d_a0, List<t_A>::nil()));
    }
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return List<t_A>::cons(d_a0, d_a1->app(m));
    }
  }
};

struct ToString {
  template <typename T1, typename T2, MapsTo<std::string, T1> F0,
            MapsTo<std::string, T2> F1>
  __attribute__((pure)) static std::string
  pair_to_string(F0 &&p1, F1 &&p2, const std::pair<T1, T2> x) {
    const T1 &a = x.first;
    const T2 &b = x.second;
    return "("s + p1(a) + ", "s + p2(b) + ")"s;
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  __attribute__((pure)) static std::string
  intersperse(F0 &&p, const std::string sep,
              const std::shared_ptr<List<T1>> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return "";
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
      if (std::holds_alternative<typename List<T1>::Nil>(d_a1->v())) {
        return sep + p(d_a0);
      } else {
        return sep + p(d_a0) + intersperse<T1>(p, sep, d_a1);
      }
    }
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  __attribute__((pure)) static std::string
  list_to_string(F0 &&p, const std::shared_ptr<List<T1>> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return "[]";
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
      if (std::holds_alternative<typename List<T1>::Nil>(d_a1->v())) {
        return "["s + p(d_a0) + "]"s;
      } else {
        return "["s + p(d_a0) + intersperse<T1>(p, "; ", d_a1) + "]"s;
      }
    }
  }
};

struct Tokenizer {
  __attribute__((pure)) static std::pair<
      std::optional<std::basic_string_view<char>>, std::basic_string_view<char>>
  next_token(const std::basic_string_view<char> input,
             const std::basic_string_view<char> soft,
             const std::basic_string_view<char> hard);
  static std::shared_ptr<List<std::basic_string_view<char>>>
  list_tokens(const std::basic_string_view<char> input,
              const std::basic_string_view<char> soft,
              const std::basic_string_view<char> hard);

  template <typename T1>
  static std::vector<T1> list_to_vec_h(const std::shared_ptr<List<T1>> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return {};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
      std::vector<T1> v = list_to_vec_h<T1>(d_a1);
      v.push_back(d_a0);
      return v;
    }
  }

  template <typename T1>
  static std::vector<T1> list_to_vec(const std::shared_ptr<List<T1>> &l) {
    return list_to_vec_h<T1>(l->rev());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::vector<T2> list_to_vec_map_h(F0 &&f,
                                           const std::shared_ptr<List<T1>> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return {};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
      std::vector<T2> v = list_to_vec_map_h<T1, T2>(f, d_a1);
      v.push_back(f(d_a0));
      return v;
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::vector<T2> list_to_vec_map(F0 &&f,
                                         const std::shared_ptr<List<T1>> &l) {
    return list_to_vec_map_h<T1, T2>(f, l->rev());
  }
};

#endif // INCLUDED_TOKENIZER
