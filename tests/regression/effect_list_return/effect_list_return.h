#ifndef INCLUDED_EFFECT_LIST_RETURN
#define INCLUDED_EFFECT_LIST_RETURN

#include <chrono>
#include <cstdint>
#include <filesystem>
#include <iostream>
#include <memory>
#include <string>
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

struct EffectListReturn {
  /// 1. list_directory returns a list
  static std::shared_ptr<List<std::string>> list_files(const std::string path);
  /// 2. create dir and verify
  static bool make_and_check(const std::string path);
  /// 3. get_time result used in pair
  static std::pair<int64_t, std::string> timestamped_line();
  /// 4. current_path as a no-arg effect
  static std::string get_cwd();
  /// 5. Chain effects with different return types
  static std::pair<bool, std::shared_ptr<List<std::string>>>
  create_and_list(const std::string dir);
};

#endif // INCLUDED_EFFECT_LIST_RETURN
