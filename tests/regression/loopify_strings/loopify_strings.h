#ifndef INCLUDED_LOOPIFY_STRINGS
#define INCLUDED_LOOPIFY_STRINGS

#include <any>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

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

struct LoopifyStrings {
  static List<uint64_t> append(const List<uint64_t> &l1, List<uint64_t> l2);
  static List<uint64_t> join_with(uint64_t sep, const List<uint64_t> &l);
  static List<uint64_t> repeat_string(const List<uint64_t> &s, uint64_t n);
  static List<uint64_t> repeat_with_sep(List<uint64_t> s,
                                        const List<uint64_t> &sep, uint64_t n);
  static List<uint64_t> string_chain_fuel(uint64_t fuel,
                                          const List<uint64_t> &s, uint64_t n,
                                          const List<uint64_t> &sep,
                                          const List<uint64_t> &end_marker);
  static List<uint64_t> string_chain(const List<uint64_t> &s, uint64_t n,
                                     const List<uint64_t> &sep,
                                     const List<uint64_t> &end_marker);
  static List<uint64_t> reverse(const List<uint64_t> &l);
  static bool list_eq(const List<uint64_t> &l1, const List<uint64_t> &l2);
  static bool is_palindrome(const List<uint64_t> &l);
  static List<uint64_t> intersperse(uint64_t sep, const List<uint64_t> &l);
  static List<uint64_t> intercalate(const List<uint64_t> &sep,
                                    const List<List<uint64_t>> &ll);
  static List<uint64_t> replicate(uint64_t n, uint64_t x);
  static List<std::pair<uint64_t, uint64_t>>
  run_length_aux(uint64_t current, uint64_t count, const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  run_length_encode(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_STRINGS
