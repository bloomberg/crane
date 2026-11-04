#ifndef INCLUDED_BOXED_ELEMENT_BLOCK_TEMPLATE
#define INCLUDED_BOXED_ELEMENT_BLOCK_TEMPLATE

#include <conslist.h>
#include <cstdint>
#include <type_traits>
#include <utility>
#include <variant>

struct ListDef {
  template <typename T1, typename T2, typename F0>
  static crane::list<T2> map(F0 &&f, const crane::list<T1> &l);
};

/// A Boxed Element container whose constructors are %result blocks.
///
/// A block's text is spliced as statements, and its %elem hole is decided
/// like a constructor template's: boxed where the element recurses through
/// the container, so list rose builds crane::list<crane::box<rose>>
/// while list nat builds crane::list<uint64_t>.
struct BoxedElementBlockTemplate {
  struct rose {
    // TYPES
    struct Node {
      uint64_t n;
      crane::list<crane::box<rose>> kids;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Node _v) : v_(std::move(_v)) {}

    static rose node(uint64_t n, crane::list<crane::box<rose>> kids) {
      return rose(Node{n, std::move(kids)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &,
                                   const crane::list<crane::box<rose>> &>
  static T1 rose_rect(F0 &&f, const rose &r) {
    const auto &[n0, kids0] = std::get<typename rose::Node>(r.v());
    return f(n0, kids0);
  }

  template <typename T1, typename F0>
  static T1 rose_rec(F0 &&f, const rose &r) {
    return rose_rect<T1>(f, r);
  }

  static uint64_t total(const rose &r);
  static crane::list<uint64_t> leaves(const rose &r);
  static inline const rose sample =
      rose::node(UINT64_C(1), []() -> crane::list<crane::box<rose>> {
        crane::list<crane::box<rose>> _r;
        _r = crane::cons(
            rose::node(UINT64_C(2),
                       []() -> crane::list<crane::box<rose>> {
                         crane::list<crane::box<rose>> _r;
                         _r = crane::list<crane::box<rose>>{};
                         return _r;
                       }()),
            []() -> crane::list<crane::box<rose>> {
              crane::list<crane::box<rose>> _r;
              _r = crane::cons(
                  rose::node(UINT64_C(3),
                             []() -> crane::list<crane::box<rose>> {
                               crane::list<crane::box<rose>> _r;
                               _r = crane::cons(
                                   rose::node(
                                       UINT64_C(4),
                                       []() -> crane::list<crane::box<rose>> {
                                         crane::list<crane::box<rose>> _r;
                                         _r = crane::list<crane::box<rose>>{};
                                         return _r;
                                       }()),
                                   []() -> crane::list<crane::box<rose>> {
                                     crane::list<crane::box<rose>> _r;
                                     _r = crane::list<crane::box<rose>>{};
                                     return _r;
                                   }());
                               return _r;
                             }()),
                  []() -> crane::list<crane::box<rose>> {
                    crane::list<crane::box<rose>> _r;
                    _r = crane::cons(
                        rose::node(UINT64_C(5),
                                   []() -> crane::list<crane::box<rose>> {
                                     crane::list<crane::box<rose>> _r;
                                     _r = crane::list<crane::box<rose>>{};
                                     return _r;
                                   }()),
                        []() -> crane::list<crane::box<rose>> {
                          crane::list<crane::box<rose>> _r;
                          _r = crane::list<crane::box<rose>>{};
                          return _r;
                        }());
                    return _r;
                  }());
              return _r;
            }());
        return _r;
      }());
  static inline const uint64_t sample_total = total(sample);
  static inline const crane::list<uint64_t> sample_leaves = leaves(sample);
};

template <typename T1, typename T2, typename F0>
crane::list<T2> ListDef::map(F0 &&f, const crane::list<T1> &l) {
  if (l.empty()) {
    return []() -> crane::list<T2> {
      crane::list<T2> _r;
      _r = crane::list<T2>{};
      return _r;
    }();
  } else {
    const T1 &a = l.front();
    auto l0 = l.tail();
    return [&]() -> crane::list<T2> {
      crane::list<T2> _r;
      _r = crane::cons(f(a), ListDef::template map<T1, T2>(f, l0));
      return _r;
    }();
  }
}

#endif // INCLUDED_BOXED_ELEMENT_BLOCK_TEMPLATE
