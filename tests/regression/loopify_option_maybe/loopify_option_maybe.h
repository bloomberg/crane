#ifndef INCLUDED_LOOPIFY_OPTION_MAYBE
#define INCLUDED_LOOPIFY_OPTION_MAYBE

#include <any>
#include <memory>
#include <optional>
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

struct LoopifyOptionMaybe {
  static std::optional<uint64_t> find_even(const List<uint64_t> &l);
  static std::optional<uint64_t> find_greater(uint64_t threshold,
                                              const List<uint64_t> &l);
  static std::optional<uint64_t>
  lookup(uint64_t key, const List<std::pair<uint64_t, uint64_t>> &l);
  static List<uint64_t>
  lookup_all(uint64_t key, const List<std::pair<uint64_t, uint64_t>> &l);
  static std::optional<uint64_t> safe_head(const List<uint64_t> &l);
  static std::optional<List<uint64_t>> safe_tail(const List<uint64_t> &l);
  static List<uint64_t> catMaybes(const List<std::optional<uint64_t>> &l);
  static std::optional<uint64_t> find_index_even_aux(const List<uint64_t> &l,
                                                     uint64_t idx);
  static std::optional<uint64_t> find_index_even(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_OPTION_MAYBE
