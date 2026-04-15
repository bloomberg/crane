#ifndef INCLUDED_EFFECT_DIR_PATH
#define INCLUDED_EFFECT_DIR_PATH

#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

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

  __attribute__((pure)) unsigned int length() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return (d_a1->length() + 1);
    }
  }
};

struct EffectDirPath {
  /// 1. list_directory result matched — exercises IIFE + list match
  static std::optional<std::string> first_file(const std::string path);
  /// 2. current_path (zero args) chained to env
  static void save_cwd();
  /// 3. is_directory bool result used in conditional with effects in arms
  static std::optional<std::string> check_and_list(const std::string path);
  /// 4. Path effect result chained to print
  static void show_absolute(const std::string path);
  /// 5. Multiple bool effects composed
  static std::string classify_path(const std::string path);
  /// 6. create_directory bool result explicitly bound and used
  static std::string create_and_report(const std::string path);
  /// 7. Recursive function counting list items from list_directory
  static unsigned int
  count_entries(const std::shared_ptr<List<std::string>> &dirs,
                const unsigned int acc);
  /// 8. remove_directory (returns bool but treated as unit in bind)
  static void cleanup(const std::string path);
};

#endif // INCLUDED_EFFECT_DIR_PATH
