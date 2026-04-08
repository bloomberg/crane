#ifndef INCLUDED_LOOPIFY_ITREE_SEQ
#define INCLUDED_LOOPIFY_ITREE_SEQ

#include <functional>
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
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

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

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyItreeSeq {
  /// Tail-recursive countdown using erased ITree. In sequential mode, itree is
  /// erased so this becomes a plain tail-recursive C++ function. Loopify should
  /// convert it to a while loop.
  static unsigned int count_down(const unsigned int n);
  /// Sum 1..n via tail recursion with accumulator.
  static unsigned int sum_to(const unsigned int n);
  /// Non-tail recursive: build a list counting down from n.
  static std::shared_ptr<List<unsigned int>>
  countdown_list(const unsigned int n);
  static unsigned int delay_ret(const unsigned int n, const unsigned int v);
  static void spin();
  static void forever(const unsigned int n);
  static unsigned int test_count_5();
  static unsigned int test_sum_10();
  static std::shared_ptr<List<unsigned int>> test_clist_4();
  static unsigned int test_delay();
};

#endif // INCLUDED_LOOPIFY_ITREE_SEQ
