#ifndef INCLUDED_LOOPIFY_OPTION_MAYBE
#define INCLUDED_LOOPIFY_OPTION_MAYBE

#include <memory>
#include <optional>
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
};

struct LoopifyOptionMaybe {
  __attribute__((pure)) static std::optional<unsigned int>
  find_even(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static std::optional<unsigned int>
  find_greater(const unsigned int threshold,
               const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static std::optional<unsigned int>
  lookup(const unsigned int key,
         const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l);
  static std::shared_ptr<List<unsigned int>> lookup_all(
      const unsigned int key,
      const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l);
  __attribute__((pure)) static std::optional<unsigned int>
  safe_head(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((
      pure)) static std::optional<std::shared_ptr<List<unsigned int>>>
  safe_tail(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  catMaybes(const std::shared_ptr<List<std::optional<unsigned int>>> &l);
  __attribute__((pure)) static std::optional<unsigned int>
  find_index_even_aux(const std::shared_ptr<List<unsigned int>> &l,
                      const unsigned int idx);
  __attribute__((pure)) static std::optional<unsigned int>
  find_index_even(const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_OPTION_MAYBE
