#ifndef INCLUDED_DOC_COMMENTS
#define INCLUDED_DOC_COMMENTS

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct DocComments {
  /// add computes the sum of two natural numbers n and m.
  /// It works by structural recursion on n.
  static uint64_t add(uint64_t n, uint64_t m);

  /// A simple pair holding two values of possibly different types.
  template <typename A, typename B> struct pair {
    /// The first element of the pair.
    A fst;
    /// The second element of the pair.
    B snd;

    // ACCESSORS
    template <typename CraneU0, typename CraneU1>
      requires crane_convertible<CraneU0, const A &> &&
               crane_convertible<CraneU1, const B &>
    operator pair<CraneU0, CraneU1>() const {
      return {crane_convert<CraneU0>(fst), crane_convert<CraneU1>(snd)};
    }
  };

  /// mylist is a polymorphic list type.
  template <typename A> struct mylist {
    // TYPES
    /// The empty list.
    struct Mynil {};

    /// Cons cell: an element followed by the rest of the list.
    struct Mycons {
      A a;
      std::shared_ptr<mylist<A>> l;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    mylist(const mylist<CraneU> &_other)
        : v_(crane_convert_spine(
              _other, std::shared_ptr<mylist<A>>(nullptr),
              [](const mylist<CraneU> &_cell) -> const mylist<CraneU> * {
                if (std::holds_alternative<typename mylist<CraneU>::Mycons>(
                        _cell.v())) {
                  return std::get<typename mylist<CraneU>::Mycons>(_cell.v())
                      .l.get();
                } else {
                  return nullptr;
                }
              },
              [&](const mylist<CraneU> &_other,
                  std::shared_ptr<mylist<A>> _below) -> variant_t {
                if (std::holds_alternative<typename mylist<CraneU>::Mynil>(
                        _other.v())) {
                  return Mynil{};
                } else {
                  const auto &[a, l] =
                      std::get<typename mylist<CraneU>::Mycons>(_other.v());
                  return Mycons{
                      [&]() -> A {
                        if constexpr (crane_convertible<A, const CraneU &>) {
                          return crane_convert<A>(a);
                        } else {
                          throw std::logic_error(
                              "unreachable: inactive constructor field at this "
                              "instantiation");
                        }
                      }(),
                      std::move(_below)};
                }
              },
              [](auto &&_alt) {
                return std::make_shared<mylist<A>>(std::move(_alt));
              })) {}

    /// The empty list.
    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    /// Cons cell: an element followed by the rest of the list.
    static mylist<A> mycons(A a, mylist<A> l) {
      return mylist<A>(
          Mycons{std::move(a), std::make_shared<mylist<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~mylist() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist<A>> {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
          }
        }
        return nullptr;
      };
      std::shared_ptr<mylist<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) = default;
    mylist &operator=(mylist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 mylist_rect(T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(a0, *a1, mylist_rect<T1, T2>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 mylist_rec(const T2 &f, F1 &&f0, const mylist<T1> &m) {
    return mylist_rect<T1, T2>(f, f0, m);
  }

  static uint64_t no_doc_comment(uint64_t x);

  /// The identity function: returns its argument unchanged.
  template <typename T1> static T1 identity(T1 x) { return x; }

  /// double n returns 2 * n.
  static uint64_t double_(uint64_t n);
  /// A simple color enumeration.
  enum class Color {
    /// Red color.
    RED,
    /// Green color.
    GREEN,
    /// Blue color.
    BLUE
  };

  template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    }
    case Color::GREEN: {
      return f0;
    }
    case Color::BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 color_rec(const T1 &f, const T1 &f0, const T1 &f1, Color c) {
    return color_rect<T1>(f, f0, f1, c);
  }
};

#endif // INCLUDED_DOC_COMMENTS
