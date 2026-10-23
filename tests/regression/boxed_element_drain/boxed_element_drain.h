#ifndef INCLUDED_BOXED_ELEMENT_DRAIN
#define INCLUDED_BOXED_ELEMENT_DRAIN

#include "small_vector.h"
#include <atomic>
#include <conslist.h>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// A rose tree over a container with a Boxed Element wrapper and a
/// Drain clause, as ParseALot's ConsList.v maps lists: the destructor
/// takes a deep tree apart through the drain rather than by recursion.
struct BoxedElementDrain {
  struct rose {
    // TYPES
    struct Node {
      uint64_t n;
      crane::list<rose> kids;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Node _v) : v_(std::move(_v)) {}

    static rose node(uint64_t n, crane::list<rose> kids) {
      return rose(Node{n, std::move(kids)});
    }

    // MANIPULATORS
    ~rose() {
      crane::small_vector<std::shared_ptr<rose>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          _alt->kids.drain_each([&](auto &&_e) {
            _stack.push_back(std::make_shared<rose>(std::move(_e)));
            ;
          });
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    rose(const rose &) = default;
    rose &operator=(const rose &) = default;
    rose(rose &&) = default;
    rose &operator=(rose &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &,
                                   const crane::list<rose> &>
  static T1 rose_rect(F0 &&f, const rose &r) {
    const auto &[n0, kids0] = std::get<typename rose::Node>(r.v());
    return f(n0, kids0);
  }

  template <typename T1, typename F0>
  static T1 rose_rec(F0 &&f, const rose &r) {
    return rose_rect<T1>(f, r);
  }

  static uint64_t total(const rose &r);
  static rose spine(uint64_t d);
  static inline const rose sample = rose::node(
      UINT64_C(2),
      crane::cons(
          rose::node(UINT64_C(3), crane::list<rose>{}),
          crane::cons(rose::node(UINT64_C(4),
                                 crane::cons(rose::node(UINT64_C(5),
                                                        crane::list<rose>{}),
                                             crane::list<rose>{})),
                      crane::list<rose>{})));

  static inline const uint64_t sample_total = total(sample);
};

#endif // INCLUDED_BOXED_ELEMENT_DRAIN
