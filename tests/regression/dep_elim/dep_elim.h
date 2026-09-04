#ifndef INCLUDED_DEP_ELIM
#define INCLUDED_DEP_ELIM

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>)
                          return crane_any_cast<A>(a);
                        else
                          return A(a);
                      }(),
                      l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
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

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct DepElim {
  struct fin {
    // TYPES
    struct FZ {
      uint64_t n;
    };

    struct FS {
      uint64_t n;
      std::shared_ptr<fin> a1;
    };

    using variant_t = std::variant<FZ, FS>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    fin() {}

    explicit fin(FZ _v) : v_(std::move(_v)) {}

    explicit fin(FS _v) : v_(std::move(_v)) {}

    static fin fz(uint64_t n) { return fin(FZ{n}); }

    static fin fs(uint64_t n, fin a1) {
      return fin(FS{n, std::make_shared<fin>(std::move(a1))});
    }

    // MANIPULATORS
    ~fin() {
      crane::small_vector<std::shared_ptr<fin>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<FS>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
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

    fin(const fin &) = default;
    fin &operator=(const fin &) = default;
    fin(fin &&) noexcept = default;
    fin &operator=(fin &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t fin_to_nat(uint64_t _x) const {
      const fin *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const fin *_self;
        uint64_t _x;
      };

      /// _Resume_FS: resumes after recursive call with _result.
      struct _Resume_FS {};

      using _Frame = std::variant<_Enter, _Resume_FS>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, _x});
      /// Loopified fin_to_nat: _Enter -> _Resume_FS.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const fin *_self = _f._self;
          uint64_t _x = _f._x;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename fin::FZ>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[n, a1] = std::get<typename fin::FS>(_sv.v());
            _stack.emplace_back(_Resume_FS{});
            _stack.emplace_back(_Enter{crane_raw(a1), n});
          }
        } else {
          auto _f = std::move(std::get<_Resume_FS>(_frame));
          _result = (std::move(_result) + 1);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, fin &, T1 &>
    T1 fin_rec(F0 &&f, F1 &&f0, uint64_t _x) const {
      const fin *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const fin *_self;
        uint64_t _x;
      };

      /// _Resume_FS: saves [a1, n0], resumes after recursive call with _result.
      struct _Resume_FS {
        fin a1;
        uint64_t n0;
      };

      using _Frame = std::variant<_Enter, _Resume_FS>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, _x});
      /// Loopified fin_rec: _Enter -> _Resume_FS.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const fin *_self = _f._self;
          uint64_t _x = _f._x;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename fin::FZ>(_sv.v())) {
            const auto &[n0] = std::get<typename fin::FZ>(_sv.v());
            _result = f(n0);
          } else {
            const auto &[n0, a1] = std::get<typename fin::FS>(_sv.v());
            _stack.emplace_back(_Resume_FS{*a1, n0});
            _stack.emplace_back(_Enter{crane_raw(a1), n0});
          }
        } else {
          auto _f = std::move(std::get<_Resume_FS>(_frame));
          _result = f0(_f.n0, std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, fin &, T1 &>
    T1 fin_rect(F0 &&f, F1 &&f0, uint64_t _x) const {
      const fin *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const fin *_self;
        uint64_t _x;
      };

      /// _Resume_FS: saves [a1, n0], resumes after recursive call with _result.
      struct _Resume_FS {
        fin a1;
        uint64_t n0;
      };

      using _Frame = std::variant<_Enter, _Resume_FS>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, _x});
      /// Loopified fin_rect: _Enter -> _Resume_FS.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const fin *_self = _f._self;
          uint64_t _x = _f._x;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename fin::FZ>(_sv.v())) {
            const auto &[n0] = std::get<typename fin::FZ>(_sv.v());
            _result = f(n0);
          } else {
            const auto &[n0, a1] = std::get<typename fin::FS>(_sv.v());
            _stack.emplace_back(_Resume_FS{*a1, n0});
            _stack.emplace_back(_Enter{crane_raw(a1), n0});
          }
        } else {
          auto _f = std::move(std::get<_Resume_FS>(_frame));
          _result = f0(_f.n0, std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }
  };

  template <typename A> struct vec {
    // TYPES
    struct Vnil {};

    struct Vcons {
      uint64_t n;
      A a1;
      std::shared_ptr<vec<A>> a2;
    };

    using variant_t = std::variant<Vnil, Vcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    vec() {}

    explicit vec(Vnil _v) : v_(_v) {}

    explicit vec(Vcons _v) : v_(std::move(_v)) {}

    template <typename _U> vec(const vec<_U> &_other) {
      if (std::holds_alternative<typename vec<_U>::Vnil>(_other.v())) {
        this->v_ = Vnil{};
      } else {
        const auto &[n, a1, a2] = std::get<typename vec<_U>::Vcons>(_other.v());
        this->v_ = Vcons{n,
                         [&]() -> A {
                           if constexpr (std::is_same_v<_U, std::any>)
                             return crane_any_cast<A>(a1);
                           else
                             return A(a1);
                         }(),
                         a2 ? std::make_shared<vec<A>>(*a2) : nullptr};
      }
    }

    static vec<A> vnil() { return vec<A>(Vnil{}); }

    static vec<A> vcons(uint64_t n, A a1, vec<A> a2) {
      return vec<A>(
          Vcons{n, std::move(a1), std::make_shared<vec<A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~vec() {
      crane::small_vector<std::shared_ptr<vec<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Vcons>(&_v)) {
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
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

    vec(const vec &) = default;
    vec &operator=(const vec &) = default;
    vec(vec &&) noexcept = default;
    vec &operator=(vec &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    vec<A> vec_tail(uint64_t) const {
      if (std::holds_alternative<typename vec<A>::Vnil>(this->v())) {
        throw std::logic_error("unreachable");
      } else {
        const auto &[n, a1, a2] = std::get<typename vec<A>::Vcons>(this->v());
        return *a2;
      }
    }

    A vec_head(uint64_t) const {
      if (std::holds_alternative<typename vec<A>::Vnil>(this->v())) {
        throw std::logic_error("unreachable");
      } else {
        const auto &[n, a1, a2] = std::get<typename vec<A>::Vcons>(this->v());
        return a1;
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &>
    vec<T1> vec_map(uint64_t, F1 &&f) const {
      std::shared_ptr<vec<T1>> _head{};
      std::shared_ptr<vec<T1>> *_write = &_head;
      const vec<A> *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename vec<A>::Vnil>(_sv.v())) {
          *_write = std::make_shared<vec<T1>>(vec<T1>::vnil());
          break;
        } else {
          const auto &[n, a1, a2] = std::get<typename vec<A>::Vcons>(_sv.v());
          auto _cell = std::make_shared<vec<T1>>(
              typename vec<T1>::Vcons(n, f(a1), nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename vec<T1>::Vcons>((*_write)->v_mut()).a2;
          _loop_self = crane_raw(a2);
          continue;
        }
      }
      return std::move(*_head);
    }

    List<A> vec_to_list(uint64_t) const {
      std::shared_ptr<List<A>> _head{};
      std::shared_ptr<List<A>> *_write = &_head;
      const vec<A> *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename vec<A>::Vnil>(_sv.v())) {
          *_write = std::make_shared<List<A>>(List<A>::nil());
          break;
        } else {
          const auto &[n, a1, a2] = std::get<typename vec<A>::Vcons>(_sv.v());
          auto _cell =
              std::make_shared<List<A>>(typename List<A>::Cons(a1, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
          _loop_self = crane_raw(a2);
          continue;
        }
      }
      return std::move(*_head);
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, A &, vec<A> &, T1 &>
    T1 vec_rec(T1 f, F1 &&f0, uint64_t _x) const {
      const vec<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const vec<A> *_self;
        uint64_t _x;
      };

      /// _Resume_Vcons: saves [a2, a1, n0], resumes after recursive call with
      /// _result.
      struct _Resume_Vcons {
        vec<A> a2;
        std::decay_t<A> a1;
        uint64_t n0;
      };

      using _Frame = std::variant<_Enter, _Resume_Vcons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, _x});
      /// Loopified vec_rec: _Enter -> _Resume_Vcons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const vec<A> *_self = _f._self;
          uint64_t _x = _f._x;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename vec<A>::Vnil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[n0, a1, a2] =
                std::get<typename vec<A>::Vcons>(_sv.v());
            _stack.emplace_back(_Resume_Vcons{*a2, a1, n0});
            _stack.emplace_back(_Enter{crane_raw(a2), n0});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Vcons>(_frame));
          _result =
              f0(_f.n0, std::move(_f.a1), std::move(_f.a2), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, A &, vec<A> &, T1 &>
    T1 vec_rect(T1 f, F1 &&f0, uint64_t _x) const {
      const vec<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const vec<A> *_self;
        uint64_t _x;
      };

      /// _Resume_Vcons: saves [a2, a1, n0], resumes after recursive call with
      /// _result.
      struct _Resume_Vcons {
        vec<A> a2;
        std::decay_t<A> a1;
        uint64_t n0;
      };

      using _Frame = std::variant<_Enter, _Resume_Vcons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, _x});
      /// Loopified vec_rect: _Enter -> _Resume_Vcons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const vec<A> *_self = _f._self;
          uint64_t _x = _f._x;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename vec<A>::Vnil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[n0, a1, a2] =
                std::get<typename vec<A>::Vcons>(_sv.v());
            _stack.emplace_back(_Resume_Vcons{*a2, a1, n0});
            _stack.emplace_back(_Enter{crane_raw(a2), n0});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Vcons>(_frame));
          _result =
              f0(_f.n0, std::move(_f.a1), std::move(_f.a2), std::move(_result));
        }
      }
      return _result;
    }
  };

  struct avail {
    // TYPES
    struct Present {
      uint64_t a0;
    };

    struct Absent {};

    using variant_t = std::variant<Present, Absent>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    avail() {}

    explicit avail(Present _v) : v_(std::move(_v)) {}

    explicit avail(Absent _v) : v_(_v) {}

    static avail present(uint64_t a0) { return avail(Present{a0}); }

    static avail absent() { return avail(Absent{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t get_present() const {
      if (std::holds_alternative<typename avail::Present>(this->v())) {
        const auto &[a0] = std::get<typename avail::Present>(this->v());
        return a0;
      } else {
        throw std::logic_error("unreachable");
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    T1 avail_rec(F0 &&f, T1 f0, bool) const {
      if (std::holds_alternative<typename avail::Present>(this->v())) {
        const auto &[a0] = std::get<typename avail::Present>(this->v());
        return f(a0);
      } else {
        return f0;
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    T1 avail_rect(F0 &&f, T1 f0, bool) const {
      if (std::holds_alternative<typename avail::Present>(this->v())) {
        const auto &[a0] = std::get<typename avail::Present>(this->v());
        return f(a0);
      } else {
        return f0;
      }
    }
  };

  static inline const uint64_t test_fin0 =
      fin::fz(UINT64_C(2)).fin_to_nat(UINT64_C(3));
  static inline const uint64_t test_fin2 =
      fin::fs(UINT64_C(2), fin::fs(UINT64_C(1), fin::fz(UINT64_C(0))))
          .fin_to_nat(UINT64_C(3));
  static inline const vec<uint64_t> my_vec = vec<uint64_t>::vcons(
      UINT64_C(2), UINT64_C(10),
      vec<uint64_t>::vcons(UINT64_C(1), UINT64_C(20),
                           vec<uint64_t>::vcons(UINT64_C(0), UINT64_C(30),
                                                vec<uint64_t>::vnil())));
  static inline const List<uint64_t> test_vec_list =
      my_vec.vec_to_list(UINT64_C(3));
  static inline const uint64_t test_vec_head = my_vec.vec_head(UINT64_C(2));
  static inline const List<uint64_t> test_vec_tail_list =
      my_vec.vec_tail(UINT64_C(2)).vec_to_list(UINT64_C(2));
  static inline const List<uint64_t> test_vec_map =
      my_vec
          .template vec_map<uint64_t>(
              UINT64_C(3), [](uint64_t n) { return (n + UINT64_C(1)); })
          .vec_to_list(UINT64_C(3));
  static inline const uint64_t test_present =
      avail::present(UINT64_C(42)).get_present();
};

#endif // INCLUDED_DEP_ELIM
