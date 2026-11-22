// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::bake: a constant computed at build time and read back as data
// ([Crane Bake c]).
//
// At extraction Crane extracts [c] on its own, with its initialiser wrapped
// in [crane::bake::root], links that unit with a driver whose [main] is
// [crane::bake::main], and runs it.  The driver writes [c]'s value as C++
// data: an image, which Crane appends to the unit's implementation file,
// and the unit's [c] is then initialised with [crane::bake::read<T>(image)]
// instead of its body.
//
// An image is a stream of 64-bit words, the bytes of its strings, and a
// table of static blocks.  The stream is a table of nodes and then the
// value.
//
// - A node is a value of a generated inductive (one with a constructor that
//   has fields) or a [crane::list] cell: what the value shares, and what
//   recurses.  Each is written once, as one row: its constructor's index and
//   its fields, a node among them as its number.  Nodes are numbered in the
//   order they are written, which is after the nodes they hold: a row only
//   names rows above it, so the value is read back as the DAG it was, front
//   to back, with no recursion.  The rows come in runs of one type each: the
//   type's number (its place, counting from 1, in the order a walk of the
//   value's type meets the node types: [walk_types]) and the run's length.
//   0 ends the table.  A [crane::list] cell is [1], its head and its tail; a
//   nil is [0].  A counted pointer ([std::shared_ptr], [bsl::shared_ptr],
//   [crane::rc]) to a node is one pointer per node again when read.
// - A scalar (integer, character, boolean, enumeration, floating point) is
//   one word, as is a constructor of an inductive whose constructors have
//   no fields.  A string ([std::string], or any type with a [traits_type],
//   an allocator and a constructor from a pointer and a length) is its
//   length; its bytes are in the image's text, in the order the strings are
//   written.  A pair ([first] and [second]), a tuple, a record or flat
//   struct (field by field) and an optional (a presence word first) are
//   their components in order; a type with no state is nothing.  A sequence
//   container ([std::vector], [std::deque], ...) and a [persistent_array]
//   (its default element after the length) are their length and elements.
//   A number with a text form ([mpz_class]: [get_str(16)] and a constructor
//   from a string and a base) is its base-16 text.
// - A [crane::shared_array] is [0] (empty), [1] (its length and elements),
//   [k + 3] (the [k]th array already read) or [2] followed by a static block
//   and its element type's code: an array of scalars, or of such arrays,
//   whose block the image declares constant-initialised with an immortal
//   count ([crane::shared_array::fixed]), so it costs nothing at startup and
//   its count is never written.
//
// The writer lays the stream out one row to a line, each with a comment
// that spells it: its number, its constructor's and fields' names, its
// scalars and strings as literals.  Strings are C++ string literals, words
// decimal.  Past [annotated_rows] rows, rows are filled into lines bare.  The
// text is cut into character arrays of at most [text_chunk] bytes, a string
// split across two where it falls on a cut.
//
// Writing walks the value with an explicit stack and reading is a loop over
// the rows, so a list or a tree as deep as memory allows is baked and read
// back.
//
// Reading builds the value once, at static initialisation, and makes every
// block it allocates immortal ([crane::make_immortal]): the value lives as
// long as the program, and reading it from any thread never touches its
// counts.
//
// The format is the same on every byte order: a word is written as the
// number it is, never as memory.  What it does assume is asserted below; and
// an image asserts that the target reads its scalars at the widths the bake
// host wrote them at ([data_model]), which is what cross-compiling a baked
// unit could break.

#pragma once

#include <algorithm>
#include <array>
#include <bit>
#include <cctype>
#include <cinttypes>
#include <climits>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <typeindex>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

#include "aggregate.h"
#include "conslist.h"
#include "field.h"
#include "shared_array.h"
#include "shared_variant.h"

template <typename T> class persistent_array;

static_assert(CHAR_BIT == 8, "crane::bake: an image packs a string's bytes eight to a 64-bit word, "
                             "so a byte must have 8 bits");
static_assert(std::numeric_limits<float>::is_iec559 && sizeof(float) == 4 &&
                  std::numeric_limits<double>::is_iec559 && sizeof(double) == 8,
              "crane::bake: an image holds a float or a double as its IEEE 754 bits in a word");
static_assert(sizeof(std::size_t) <= sizeof(std::uint64_t),
              "crane::bake: an image holds a length in a 64-bit word");

namespace crane::bake {

// A baked value as the generated implementation file holds it.
struct image {
  const std::uint64_t *words;
  std::size_t size;
  const void *const *blocks;
  std::size_t block_count;
  // The strings' bytes, in the order they are written, as consecutive
  // chunks: each is one string literal, which C++ compilers need only
  // support up to 65536 bytes long ([-Woverlength-strings]).
  const std::string_view *text;
  std::size_t text_chunks;
};

// The widths of the scalar types an image may hold, which the bake host and
// the target must agree on: each image asserts it equals the host's.
inline constexpr std::uint64_t data_model =
    std::uint64_t(sizeof(short)) | std::uint64_t(sizeof(int)) << 8 | std::uint64_t(sizeof(long)) << 16 |
    std::uint64_t(sizeof(long long)) << 24 | std::uint64_t(sizeof(wchar_t)) << 32 |
    std::uint64_t(sizeof(std::size_t)) << 40;

namespace detail {

template <class T> struct is_std_tuple : std::false_type {};
template <class... A> struct is_std_tuple<std::tuple<A...>> : std::true_type {};
template <class T> struct is_list : std::false_type {};
template <class A> struct is_list<crane::list<A>> : std::true_type {};
template <class T> struct is_shared_array : std::false_type {};
template <class A> struct is_shared_array<crane::shared_array<A>> : std::true_type {};
template <class T> struct is_persistent_array : std::false_type {};
template <class A> struct is_persistent_array<::persistent_array<A>> : std::true_type {
  using element = A;
};

// A handle to one value of another type, written in place: what it points
// to, and whether it shares that value by identity ([counted]), which
// reading then keeps, rather than by the value's own node sharing.
template <class P> struct handle : std::false_type {};
// A shared pointer: [std::shared_ptr], or another library's with its
// interface ([bsl::shared_ptr]), which takes ownership of a new element.
template <class P>
concept shared_pointer = requires(const P &p) {
  typename P::element_type;
  p.use_count();
  { p.get() } -> std::convertible_to<const typename P::element_type *>;
} && std::is_constructible_v<P, typename P::element_type *>;
template <class P>
  requires shared_pointer<P>
struct handle<P> : std::true_type {
  using element = typename P::element_type;
  static constexpr bool counted = true;
  static P make(element &&a) {
    if constexpr (std::is_same_v<P, std::shared_ptr<element>>)
      return std::make_shared<element>(std::move(a));
    else
      return P(new element(std::move(a)));
  }
};
template <class A> struct handle<crane::rc<A>> : std::true_type {
  using element = A;
  static constexpr bool counted = true;
  static crane::rc<A> make(A &&a) { return crane::make_rc<A>(std::move(a)); }
};
template <class A> struct handle<crane::shared_box<A>> : std::true_type {
  using element = A;
  static constexpr bool counted = false;
  static crane::shared_box<A> make(A &&a) { return crane::shared_box<A>::make(std::move(a)); }
};
template <class A> struct handle<crane::field_box<A>> : std::true_type {
  using element = A;
  static constexpr bool counted = false;
  static crane::field_box<A> make(A &&a) { return crane::field_box<A>(std::move(a)); }
};
// A [crane::list]'s boxed element (a mapping's [Boxed Element]).
template <class A> struct handle<crane::box<A>> : std::true_type {
  using element = A;
  static constexpr bool counted = true;
  static crane::box<A> make(A &&a) { return crane::box<A>(std::move(a)); }
};

// A field of a node of type [T] that holds another node of type [T]: the
// spine the writer and reader walk with an explicit stack.
template <class F, class T>
concept self_handle = handle<F>::value && std::is_same_v<typename handle<F>::element, T>;

template <class T>
concept string_like = requires(const T &s, const char *p, std::size_t n) {
  typename T::traits_type;
  typename T::allocator_type;
  { s.data() } -> std::convertible_to<const char *>;
  { s.size() } -> std::convertible_to<std::size_t>;
  T(p, n);
};

template <class T>
concept pair_like = requires(const T &x) {
  typename T::first_type;
  typename T::second_type;
  x.first;
  x.second;
} && std::is_constructible_v<T, typename T::first_type &&, typename T::second_type &&>;

template <class T>
concept optional_like = requires(const T &x) {
  typename T::value_type;
  { x.has_value() } -> std::same_as<bool>;
  *x;
} && std::is_default_constructible_v<T> && std::is_constructible_v<T, typename T::value_type &&>;

// A number whose base-16 text is what it is ([mpz_class]).
template <class T>
concept textual_number = requires(const T &x) {
  { x.get_str(16) } -> std::convertible_to<std::string>;
} && std::is_constructible_v<T, const std::string &, int>;

// A sequence container: built back element by element.
template <class T>
concept sequence = requires(T &c, const T &x, typename T::value_type &&e) {
  typename T::allocator_type;
  x.begin();
  x.end();
  { x.size() } -> std::convertible_to<std::size_t>;
  c.push_back(std::move(e));
} && std::is_default_constructible_v<T>;

// The alternatives of a variant: std::variant, crane::variant or
// crane::shared_variant.
template <class V> struct alternatives;
template <template <class...> class V, class... Ts> struct alternatives<V<Ts...>> {
  using type = std::tuple<Ts...>;
};

// A generated inductive: its variant, the alternatives' structs, and a
// constructor from each.
template <class T>
concept inductive = requires(const T &t) {
  typename T::variant_t;
  t.v();
};

// A record or a flat struct: an aggregate read field by field.
template <class T>
concept fielded = std::is_aggregate_v<T> && std::is_class_v<T> && !std::is_empty_v<T>;

template <class A> using fields_t = aggregate::fields_t<A>;

template <class A, class F> void each(const A &a, F &&f) { aggregate::each(a, f); }

template <std::size_t K, class A> const auto &field_at(const A &a) { return aggregate::get<K>(a); }

template <std::size_t I, class V> const auto &alt_at(const V &v) {
  using std::get;
  return get<I>(v);
}

template <class F, std::size_t... I> void on_index(std::size_t i, F &&f, std::index_sequence<I...>) {
  (void)((i == I ? (f(std::integral_constant<std::size_t, I>{}), true) : false) || ...);
}

// A scalar's literal type has a static block only if it can be spelled.
template <class E> constexpr const char *scalar_name() {
  if constexpr (std::is_same_v<E, bool>) return "bool";
  else if constexpr (std::is_same_v<E, char>) return "char";
  else if constexpr (std::is_same_v<E, signed char>) return "signed char";
  else if constexpr (std::is_same_v<E, unsigned char>) return "unsigned char";
  else if constexpr (std::is_same_v<E, short>) return "short";
  else if constexpr (std::is_same_v<E, unsigned short>) return "unsigned short";
  else if constexpr (std::is_same_v<E, int>) return "int";
  else if constexpr (std::is_same_v<E, unsigned int>) return "unsigned int";
  else if constexpr (std::is_same_v<E, long>) return "long";
  else if constexpr (std::is_same_v<E, unsigned long>) return "unsigned long";
  else if constexpr (std::is_same_v<E, long long>) return "long long";
  else if constexpr (std::is_same_v<E, unsigned long long>) return "unsigned long long";
  else if constexpr (std::is_same_v<E, float>) return "float";
  else if constexpr (std::is_same_v<E, double>) return "double";
  else return nullptr;
}

template <class E> constexpr bool static_element() {
  if constexpr (scalar_name<E>() != nullptr) return true;
  else if constexpr (is_shared_array<E>::value) return static_element<typename E::value_type>();
  else return false;
}

// The code a static block records of its element type, which reading
// checks: a block is only ever adopted at the type it was written at.
template <class E> constexpr std::uint64_t type_code() {
  if constexpr (is_shared_array<E>::value) return 0x100 + 31 * type_code<typename E::value_type>();
  else {
    std::uint64_t kind = std::is_same_v<E, bool>            ? 1
                         : std::is_floating_point_v<E>      ? 2
                         : std::is_signed_v<E>              ? 3
                                                            : 4;
    return kind * 16 + sizeof(E);
  }
}

template <class T> constexpr bool dependent_false = false;

// A scalar fits a word: an integer of at most 64 bits, a float or a double.
template <class T> constexpr void check_scalar() {
  static_assert(std::is_enum_v<T> || std::is_same_v<T, float> || std::is_same_v<T, double> ||
                    (std::is_integral_v<T> && sizeof(T) <= sizeof(std::uint64_t)),
                "crane::bake: a scalar wider than a word (long double, a 128-bit integer) has no image");
}

template <class T> std::uint64_t to_word(T x) {
  check_scalar<T>();
  if constexpr (std::is_enum_v<T>) return static_cast<std::uint64_t>(static_cast<std::underlying_type_t<T>>(x));
  else if constexpr (std::is_same_v<T, float>) return std::bit_cast<std::uint32_t>(x);
  else if constexpr (std::is_same_v<T, double>) return std::bit_cast<std::uint64_t>(x);
  else if constexpr (std::is_signed_v<T>) return static_cast<std::uint64_t>(static_cast<std::int64_t>(x));
  else return static_cast<std::uint64_t>(x);
}

template <class T> T of_word(std::uint64_t w) {
  check_scalar<T>();
  if constexpr (std::is_enum_v<T>) return static_cast<T>(static_cast<std::underlying_type_t<T>>(w));
  else if constexpr (std::is_same_v<T, float>) return std::bit_cast<float>(static_cast<std::uint32_t>(w));
  else if constexpr (std::is_same_v<T, double>) return std::bit_cast<double>(w);
  else if constexpr (std::is_signed_v<T>) return static_cast<T>(static_cast<std::int64_t>(w));
  else return static_cast<T>(w);
}

} // namespace detail

namespace detail {

// An inductive none of whose constructors has a field: one word, as an
// enumeration is, so the two read each other.
template <class T> constexpr bool all_nullary() {
  using alts = typename alternatives<typename T::variant_t>::type;
  return []<std::size_t... I>(std::index_sequence<I...>) {
    return (std::is_empty_v<std::tuple_element_t<I, alts>> && ...);
  }(std::make_index_sequence<std::tuple_size_v<alts>>{});
}

// A value with a row of its own, which other values name by number.
template <class T> constexpr bool is_node() {
  if constexpr (is_list<T>::value) return true;
  else if constexpr (inductive<T>) return !all_nullary<T>();
  else return false;
}

// The node types a value of [T] can hold, each once, in the order a walk of
// [T]'s definition meets them ([v.template enter<N>()] is true the first
// time): how the writer and the reader number them alike.  The cases are
// [put]'s, in its order.
template <class T, class V> void walk_types(V &v) {
  if constexpr (std::is_enum_v<T> || std::is_arithmetic_v<T> || string_like<T>) {
  } else if constexpr (pair_like<T>) {
    walk_types<typename T::first_type>(v);
    walk_types<typename T::second_type>(v);
  } else if constexpr (is_std_tuple<T>::value) {
    [&]<std::size_t... K>(std::index_sequence<K...>) {
      (walk_types<std::tuple_element_t<K, T>>(v), ...);
    }(std::make_index_sequence<std::tuple_size_v<T>>{});
  } else if constexpr (optional_like<T>) {
    walk_types<typename T::value_type>(v);
  } else if constexpr (handle<T>::value) {
    walk_types<typename handle<T>::element>(v);
  } else if constexpr (is_list<T>::value) {
    if (v.template enter<T>()) walk_types<typename T::value_type>(v);
  } else if constexpr (is_shared_array<T>::value) {
    walk_types<typename T::value_type>(v);
  } else if constexpr (is_persistent_array<T>::value) {
    walk_types<typename is_persistent_array<T>::element>(v);
  } else if constexpr (inductive<T>) {
    if constexpr (is_node<T>()) {
      if (v.template enter<T>()) {
        using alts = typename alternatives<typename T::variant_t>::type;
        [&]<std::size_t... I>(std::index_sequence<I...>) {
          (
              [&] {
                using A = std::tuple_element_t<I, alts>;
                if constexpr (!std::is_empty_v<A>)
                  [&]<std::size_t... K>(std::index_sequence<K...>) {
                    (walk_types<std::tuple_element_t<K, fields_t<A>>>(v), ...);
                  }(std::make_index_sequence<std::tuple_size_v<fields_t<A>>>{});
              }(),
              ...);
        }(std::make_index_sequence<std::tuple_size_v<alts>>{});
      }
    }
  } else if constexpr (std::is_empty_v<T> || textual_number<T>) {
  } else if constexpr (sequence<T>) {
    walk_types<typename T::value_type>(v);
  } else if constexpr (fielded<T>) {
    [&]<std::size_t... K>(std::index_sequence<K...>) {
      (walk_types<std::tuple_element_t<K, fields_t<T>>>(v), ...);
    }(std::make_index_sequence<std::tuple_size_v<fields_t<T>>>{});
  }
}

// What the writer's comments call things.  [T]'s name as the compiler spells
// it ([__PRETTY_FUNCTION__], clang's or GCC's form), and its last component:
// a constructor's alternative struct [List<bool>::Cons] is [Cons].
template <class T> std::string type_name() {
  std::string_view p = __PRETTY_FUNCTION__;
  std::size_t b = p.find("T = ");
  if (b == std::string_view::npos) return "?";
  b += 4;
  std::size_t e = p.find_first_of(";]", b);
  return std::string(p.substr(b, e == std::string_view::npos ? std::string_view::npos : e - b));
}

inline std::string last_component(const std::string &name) {
  int depth = 0;
  for (std::size_t i = name.size(); i > 1; --i) {
    char c = name[i - 1];
    if (c == '>') ++depth;
    else if (c == '<') --depth;
    else if (c == ':' && name[i - 2] == ':' && depth == 0) return name.substr(i);
  }
  return name;
}

// The names of an aggregate's fields, through clang's [__builtin_dump_struct]
// (each field's line is [indent, type, name, value]; [indent] is two spaces
// at the top level); [_0], [_1], ... without it.
template <class A> const std::vector<std::string> &field_names(const A &a) {
  static const std::vector<std::string> names = [&] {
    std::vector<std::string> ns;
#if defined(__has_builtin)
#if __has_builtin(__builtin_dump_struct)
    __builtin_dump_struct(&a, [&](const char *, auto... args) {
      if constexpr (sizeof...(args) >= 3) {
        auto t = std::make_tuple(args...);
        if constexpr (std::is_convertible_v<std::tuple_element_t<0, decltype(t)>, const char *> &&
                      std::is_convertible_v<std::tuple_element_t<2, decltype(t)>, const char *>)
          if (std::strcmp(std::get<0>(t), "  ") == 0) ns.push_back(std::get<2>(t));
      }
      return 0;
    });
#endif
#endif
    constexpr std::size_t n = std::tuple_size_v<fields_t<A>>;
    if (ns.size() != n) {
      ns.clear();
      for (std::size_t i = 0; i < n; ++i) ns.push_back("_" + std::to_string(i));
    }
    return ns;
  }();
  return names;
}

// An enumerator's name, read off [__PRETTY_FUNCTION__] for a scoped
// enumeration's first 64 values; empty where it has none.
template <auto V> constexpr std::string_view enumerator_text() { return __PRETTY_FUNCTION__; }

template <class E> std::string enumerator_name(std::uint64_t w) {
  if constexpr (std::is_convertible_v<E, int>) {
    return "";
  } else {
    constexpr std::size_t n = 64;
    if (w >= n) return "";
    static const auto texts = []<std::size_t... I>(std::index_sequence<I...>) {
      return std::array<std::string_view, n>{enumerator_text<static_cast<E>(I)>()...};
    }(std::make_index_sequence<n>{});
    std::string_view p = texts[w];
    std::size_t b = p.find("V = ");
    if (b == std::string_view::npos) return "";
    b += 4;
    std::size_t e = p.find_first_of(";]", b);
    std::string s(p.substr(b, e == std::string_view::npos ? std::string_view::npos : e - b));
    if (s.empty() || s[0] == '(' || (s[0] >= '0' && s[0] <= '9') || s[0] == '-') return "";
    return last_component(s);
  }
}

// A C++ string literal of [n] bytes at [p]: printable ASCII as itself,
// anything else escaped (a hex escape ends its literal, so a hex digit after
// it does not join it), and a [?] after a [?] as [\?], so no trigraph
// ([??=]) is spelled, as Crane's printer writes string literals
// (emit/print.ml, [escape_cpp_string]).
inline std::string quoted(const char *p, std::size_t n) {
  std::string out = "\"";
  for (std::size_t i = 0; i < n; ++i) {
    unsigned char c = static_cast<unsigned char>(p[i]);
    switch (c) {
    case '?': out += i > 0 && p[i - 1] == '?' ? "\\?" : "?"; break;
    case '"': out += "\\\""; break;
    case '\\': out += "\\\\"; break;
    case '\n': out += "\\n"; break;
    case '\t': out += "\\t"; break;
    case '\r': out += "\\r"; break;
    default:
      if (c >= 0x20 && c < 0x7f) {
        out += static_cast<char>(c);
      } else {
        char buf[8];
        std::snprintf(buf, sizeof buf, "\\x%02x", c);
        out += buf;
        if (i + 1 < n && std::isxdigit(static_cast<unsigned char>(p[i + 1]))) out += "\" \"";
      }
    }
  }
  return out + "\"";
}

// A floating-point number as the shortest literal that reads back as it.
template <class F> std::string float_literal(F x) {
  const char *suffix = std::is_same_v<F, float> ? "f" : "";
  const char *type = std::is_same_v<F, float> ? "float" : "double";
  if (x != x) return std::string("std::numeric_limits<") + type + ">::quiet_NaN()";
  if (x == std::numeric_limits<F>::infinity()) return std::string("std::numeric_limits<") + type + ">::infinity()";
  if (x == -std::numeric_limits<F>::infinity())
    return std::string("-std::numeric_limits<") + type + ">::infinity()";
  char buf[64];
  for (int prec = 1; prec <= 17; ++prec) {
    std::snprintf(buf, sizeof buf, "%.*g", prec, static_cast<double>(x));
    if (static_cast<F>(std::strtod(buf, nullptr)) == x) break;
  }
  std::string s = buf;
  if (s.find_first_of(".en") == std::string::npos) s += ".0";
  return s + suffix;
}

// A scalar as a C++ literal of its own type.
template <class E> std::string scalar_literal(const E &x) {
  char buf[64];
  if constexpr (std::is_same_v<E, bool>) return x ? "true" : "false";
  else if constexpr (std::is_floating_point_v<E>) return float_literal(x);
  else if constexpr (std::is_signed_v<E>) {
    long long v = x;
    if (v == std::numeric_limits<long long>::min()) return "(-9223372036854775807LL - 1)";
    std::snprintf(buf, sizeof buf, "%lld", v);
  } else {
    unsigned long long v = x;
    std::snprintf(buf, sizeof buf, v > static_cast<unsigned long long>(std::numeric_limits<long long>::max()) ? "%lluu" : "%llu", v);
  }
  return buf;
}

// A word as a literal of [std::uint64_t].
inline std::string word_literal(std::uint64_t w) {
  char buf[32];
  std::snprintf(buf, sizeof buf, w > static_cast<std::uint64_t>(std::numeric_limits<std::int64_t>::max()) ? "%" PRIu64 "u" : "%" PRIu64, w);
  return buf;
}

} // namespace detail

// Writes a value as an image (the bake driver's side).
class writer {
public:
  // How many rows get a comment; the rest are filled into lines bare.
  static constexpr std::size_t annotated_rows = 1000;

private:
  std::vector<std::uint64_t> words_;
  // The stream's lines: the words [begin, end), the comment that spells
  // them, and what they are: a node's row, or a run's header, which past
  // [annotated_rows] rows go uncommented, or the table's end or the value.
  enum class kind { row, run, other };
  struct line {
    std::size_t begin, end;
    std::string note;
    kind what;
  };
  std::vector<line> lines_;
  // The node types, numbered as [detail::walk_types] meets them.
  struct types {
    std::unordered_map<std::type_index, std::size_t> ordinal;
    std::vector<std::string> names;
    template <class N> bool enter() {
      if (!ordinal.emplace(typeid(N), names.size()).second) return false;
      names.push_back(detail::type_name<N>());
      return true;
    }
  } types_;
  // The nodes written, per type, by identity, and how many.
  std::unordered_map<std::type_index, std::unordered_map<const void *, std::size_t>> nodes_;
  std::size_t node_count_ = 0;
  // The run being written: its type, and the line of its header.
  std::size_t run_type_ = std::size_t(-1), run_line_ = 0, run_first_ = 0;
  // The strings' bytes, and where each string ends in them.
  std::string text_;
  std::vector<std::size_t> text_ends_;
  // The arrays written, per type, by address.
  std::unordered_map<std::type_index, std::unordered_map<const void *, std::size_t>> arrays_;
  // Static blocks: their declarations, by address; the ones the stream names.
  std::string decls_;
  std::unordered_map<const void *, std::string> block_names_;
  std::vector<std::string> stream_blocks_;
  std::unordered_map<const void *, std::size_t> stream_block_index_;
  std::string prefix_;
  // The nodes left to write, each after the nodes it holds.
  struct task {
    std::type_index type;
    const void *key;
    std::function<void()> expand, emit;
    bool expanded;
  };
  std::vector<task> tasks_;

  template <class P> static void check_not_null(const P &p) {
    if constexpr (requires { static_cast<bool>(p); })
      if (!p) {
        std::fprintf(stderr, "crane::bake: a null pointer in the value\n");
        std::exit(2);
      }
  }

  // A node's identity: its alternative's address, or for a constructor
  // without fields the constructor (all its values are one row); a list
  // cell's head, or for nil none.
  template <class T> static const void *key_of(const T &x) {
    if constexpr (detail::is_list<T>::value) {
      return x.empty() ? nullptr : static_cast<const void *>(&*x.begin());
    } else {
      using alts = typename detail::alternatives<typename T::variant_t>::type;
      const auto &v = x.v();
      const void *k = nullptr;
      detail::on_index(v.index(), [&](auto i) {
        constexpr std::size_t I = decltype(i)::value;
        if constexpr (std::is_empty_v<std::tuple_element_t<I, alts>>)
          k = reinterpret_cast<const void *>(std::uintptr_t(I + 1));
        else
          k = &detail::alt_at<I>(v);
      }, std::make_index_sequence<std::tuple_size_v<alts>>{});
      return k;
    }
  }

  template <class T> std::size_t node_number(const T &x) {
    auto &m = nodes_[typeid(T)];
    auto it = m.find(key_of(x));
    if (it == m.end()) {
      std::fprintf(stderr, "crane::bake: a node named before it is written\n");
      std::exit(2);
    }
    return it->second;
  }

  // Starts the row of a node of type [T] with identity [key]: its number.
  template <class T> std::size_t begin_row(const void *key) {
    std::size_t type = types_.ordinal.at(typeid(T));
    if (type != run_type_) {
      run_type_ = type;
      run_first_ = node_count_;
      run_line_ = lines_.size();
      lines_.push_back({words_.size(), words_.size() + 2, "", kind::run});
      words_.push_back(type + 1);
      words_.push_back(0);
    }
    ++words_[lines_[run_line_].begin + 1];
    lines_[run_line_].note = types_.names[type] + ": " + node_range(run_first_, node_count_ + 1);
    lines_.push_back({words_.size(), 0, "#" + std::to_string(node_count_) + " ", kind::row});
    nodes_[typeid(T)].emplace(key, node_count_);
    return node_count_++;
  }

  void end_row() { lines_.back().end = words_.size(); }

  static std::string node_range(std::size_t first, std::size_t end) {
    if (end == first + 1) return "#" + std::to_string(first);
    return "#" + std::to_string(first) + " to #" + std::to_string(end - 1);
  }

  void push_task(std::type_index type, const void *key, std::function<void()> expand,
                 std::function<void()> emit) {
    tasks_.push_back(task{type, key, std::move(expand), std::move(emit), false});
  }

  bool written(std::type_index type, const void *key) {
    auto it = nodes_.find(type);
    return it != nodes_.end() && it->second.count(key);
  }

  // The nodes [x] holds, outside other nodes: stacked to be written.  [x]
  // is in place in the value, never a copy: a node is known by its address,
  // and its task keeps a pointer to it.  So every container is walked by
  // reference ([persistent_array::ref], not [get], which copies).
  template <class T> void deps(const T &x) {
    using namespace detail;
    if constexpr (std::is_enum_v<T> || std::is_arithmetic_v<T> || string_like<T>) {
    } else if constexpr (pair_like<T>) {
      deps(x.first);
      deps(x.second);
    } else if constexpr (is_std_tuple<T>::value) {
      std::apply([&](const auto &...e) { (deps(e), ...); }, x);
    } else if constexpr (optional_like<T>) {
      if (x.has_value()) deps(*x);
    } else if constexpr (handle<T>::value) {
      check_not_null(x);
      deps(*x);
    } else if constexpr (is_list<T>::value) {
      push_cell<typename T::value_type>(x.begin(), x.end());
    } else if constexpr (is_shared_array<T>::value) {
      if constexpr (!static_element<typename T::value_type>())
        for (const auto &e : x) deps(e);
    } else if constexpr (is_persistent_array<T>::value) {
      std::int64_t n = x.length();
      deps(x.ref(n));  // out of bounds: the default element
      for (std::int64_t i = 0; i < n; ++i) deps(x.ref(i));
    } else if constexpr (inductive<T>) {
      if constexpr (is_node<T>()) push_node(x);
    } else if constexpr (std::is_empty_v<T> || textual_number<T>) {
    } else if constexpr (sequence<T>) {
      for (const auto &e : x) deps(e);
    } else if constexpr (fielded<T>) {
      each(x, [&](const auto &f) { deps(f); });
    }
  }

  template <class T> void push_node(const T &x) {
    using alts = typename detail::alternatives<typename T::variant_t>::type;
    using all_alts = std::make_index_sequence<std::tuple_size_v<alts>>;
    const T *p = &x;
    push_task(
        typeid(T), key_of(x),
        [this, p] {
          const auto &v = p->v();
          detail::on_index(v.index(), [&](auto i) {
            constexpr std::size_t I = decltype(i)::value;
            if constexpr (!std::is_empty_v<std::tuple_element_t<I, alts>>)
              detail::each(detail::alt_at<I>(v), [&](const auto &f) { deps(f); });
          }, all_alts{});
        },
        [this, p] {
          const auto &v = p->v();
          begin_row<T>(key_of(*p));
          std::string &note = lines_.back().note;
          detail::on_index(v.index(), [&](auto i) {
            constexpr std::size_t I = decltype(i)::value;
            using A = std::tuple_element_t<I, alts>;
            words_.push_back(I);
            note += detail::last_component(detail::type_name<A>());
            if constexpr (!std::is_empty_v<A>) {
              const A &a = detail::alt_at<I>(v);
              put_fields(a, note);
            }
          }, all_alts{});
          end_row();
        });
  }

  template <class E>
  void push_cell(typename crane::list<E>::const_iterator it, typename crane::list<E>::const_iterator end) {
    using L = crane::list<E>;
    if (it == end) {
      push_task(typeid(L), nullptr, [] {}, [this] {
        begin_row<L>(nullptr);
        words_.push_back(0);
        lines_.back().note += "nil";
        end_row();
      });
      return;
    }
    push_task(
        typeid(L), &*it,
        [this, it, end] {
          deps(*it);
          auto next = it;
          ++next;
          push_cell<E>(next, end);
        },
        [this, it, end] {
          auto next = it;
          ++next;
          begin_row<L>(&*it);
          std::string &note = lines_.back().note;
          words_.push_back(1);
          note += "cons{head = ";
          put(*it, note);
          std::size_t tail = nodes_[typeid(L)].at(next == end ? nullptr : static_cast<const void *>(&*next));
          words_.push_back(tail);
          note += ", tail = #" + std::to_string(tail) + "}";
          end_row();
        });
  }

  // An aggregate's fields, each named in [note]: [{a = 1, b = #2}].
  template <class A> void put_fields(const A &a, std::string &note) {
    const auto &names = detail::field_names(a);
    std::size_t k = 0;
    note += "{";
    detail::each(a, [&](const auto &f) {
      note += (k ? ", " : "") + names[k] + " = ";
      ++k;
      put(f, note);
    });
    note += "}";
  }

  void put_text(const char *p, std::size_t n, std::string &note) {
    words_.push_back(n);
    text_.append(p, n);
    text_ends_.push_back(text_.size());
    note += detail::quoted(p, n);
  }

  template <class E> static std::string type_spelling() {
    if constexpr (detail::is_shared_array<E>::value)
      return "crane::shared_array<" + type_spelling<typename E::value_type>() + ">";
    else return detail::scalar_name<E>();
  }

  // The name of [a]'s static block, declaring it (and the blocks it holds)
  // the first time.
  template <class E> std::string static_block(const crane::shared_array<E> &a) {
    auto it = block_names_.find(a.begin());
    if (it != block_names_.end()) return it->second;
    std::vector<std::string> elems;
    elems.reserve(a.size());
    for (const E &x : a) {
      if constexpr (detail::is_shared_array<E>::value) {
        if (x.empty()) elems.push_back(type_spelling<E>() + "{}");
        else elems.push_back(type_spelling<E>() + "::of_static(" + static_block(x) + ")");
      } else
        elems.push_back(detail::scalar_literal(x));
    }
    std::string name = prefix_ + "b" + std::to_string(block_names_.size());
    decls_ += declaration("[[clang::no_destroy]] constinit " + type_spelling<crane::shared_array<E>>() + "::fixed<" +
                              std::to_string(a.size()) + "> " + name,
                          elems);
    block_names_.emplace(a.begin(), name);
    return name;
  }

  // The declaration [head{elems};], laid out as Crane lays out the code the
  // image follows (emit/layout.ml: LLVM style, 80 columns): on one line if it
  // fits, else broken after the brace and the elements filled into lines
  // indented four columns.  The image is not handed to that layout, which
  // gives each element of a braced list too long for one line a line of its
  // own.
  static std::string declaration(const std::string &head, const std::vector<std::string> &elems) {
    constexpr std::size_t limit = 80;
    std::string one = head + "{";
    for (std::size_t i = 0; i < elems.size(); ++i) one += (i ? ", " : "") + elems[i];
    one += "};\n";
    if (one.size() - 1 <= limit) return one;
    std::string out = head + "{";
    std::size_t col = limit;
    for (std::size_t i = 0; i < elems.size(); ++i) {
      bool last = i + 1 == elems.size();
      std::size_t width = elems[i].size() + (last ? 2 : 1);
      if (col + 1 + width > limit) {
        out += "\n    ";
        col = 4;
      } else {
        out += " ";
        ++col;
      }
      out += elems[i];
      out += last ? "};" : ",";
      col += width;
    }
    return out + "\n";
  }

  // The longest string literal the image declares: what C++ compilers are
  // required to support, less the terminating null.
  static constexpr std::size_t text_chunk = 65535;

  // The text's bytes [begin, end) as one character array: each string's
  // bytes in it as literals filled into lines of 80 columns, a string too
  // long for a line split across literals.
  std::string text_declaration(const std::string &name, std::size_t begin, std::size_t end) const {
    constexpr std::size_t limit = 80, room = limit - 6;
    std::string out = "constinit const char " + name + "[] =";
    std::size_t col = out.size();
    auto add = [&](const std::string &lit, bool last) {
      if (col + 1 + lit.size() + (last ? 1 : 0) > limit) {
        out += "\n   ";
        col = 3;
      }
      out += " " + lit;
      col += 1 + lit.size();
    };
    // The first string ending past [begin].
    auto it = std::upper_bound(text_ends_.begin(), text_ends_.end(), begin);
    std::size_t pos = begin;
    std::vector<std::string> lits;
    while (pos < end) {
      std::size_t stop = std::min(end, it == text_ends_.end() ? end : *it);
      if (stop == pos) {  // an empty string
        ++it;
        continue;
      }
      // A piece whose literal fits a line, however each byte is escaped (at
      // most [\x00" "], 7 columns).
      std::size_t piece = pos, width = 2;
      while (piece < stop) {
        unsigned char c = static_cast<unsigned char>(text_[piece]);
        std::size_t w = c >= 0x20 && c < 0x7f ? (c == '"' || c == '\\' || c == '?' ? 2 : 1) : 7;
        if (width + w > room && piece > pos) break;
        width += w;
        ++piece;
      }
      lits.push_back(detail::quoted(text_.data() + pos, piece - pos));
      pos = piece;
      if (pos == stop && it != text_ends_.end()) ++it;
    }
    for (std::size_t i = 0; i < lits.size(); ++i) add(lits[i], i + 1 == lits.size());
    return out + ";\n";
  }

  // The stream's words, a line each with its comment aligned after it; a
  // line too wide for its comment takes it on a line of its own above.  Past
  // [annotated_rows] rows, rows are filled into lines bare.
  std::string stream_lines() const {
    constexpr std::size_t limit = 80, max_column = 40;
    auto words_of = [&](const line &l) {
      std::string s;
      for (std::size_t i = l.begin; i < l.end; ++i) s += (i > l.begin ? " " : "") + detail::word_literal(words_[i]) + ",";
      return s;
    };
    auto words_list = [&](const line &l) {
      std::vector<std::string> v;
      for (std::size_t i = l.begin; i < l.end; ++i) v.push_back(detail::word_literal(words_[i]));
      return v;
    };
    auto fill = [&](const std::vector<std::string> &ws) {
      std::string out, cur = "   ";
      for (const auto &w : ws) {
        if (cur.size() + 1 + w.size() + 1 > limit) {
          out += cur + "\n";
          cur = "   ";
        }
        cur += " " + w + ",";
      }
      if (cur.size() > 3) out += cur + "\n";
      return out;
    };
    // A comment too long for the end of its line, above it: broken after
    // a comma where it can be, and cut at [max_note] characters.  No line
    // ends with a backslash, which would join the next line to the comment.
    auto comment_lines = [&](std::string note) {
      constexpr std::size_t max_note = 480, room = limit - 7;
      if (note.size() > max_note) {
        std::size_t cut = max_note;
        while (cut > 0 && note[cut - 1] == '\\') --cut;
        note = note.substr(0, cut) + "...";
      }
      std::string out;
      while (!note.empty()) {
        std::size_t cut = note.size();
        if (cut > room) {
          std::size_t comma = note.rfind(", ", room - 1), space = note.rfind(' ', room - 1),
                      scope = note.rfind("::", room - 2);
          if (comma != std::string::npos && comma > room / 2) cut = comma + 1;
          else if (space != std::string::npos && space > room / 3) cut = space;
          else if (scope != std::string::npos && scope > room / 3) cut = scope + 2;
          else cut = room;
          while (cut > 1 && note[cut - 1] == '\\') --cut;
        }
        out += "    // " + note.substr(0, cut) + "\n";
        note.erase(0, cut);
        if (!note.empty() && note[0] == ' ') note.erase(0, 1);
      }
      return out;
    };
    // Whether a line has a comment, [rows] the rows before it.
    auto annotated = [](const line &l, std::size_t rows) { return l.what == kind::other || rows < annotated_rows; };
    // The comment column: past the widest annotated line that fits.
    std::size_t column = 0, rows = 0;
    for (const auto &l : lines_) {
      bool annotate = annotated(l, rows);
      if (l.what == kind::row) ++rows;
      if (!annotate) continue;
      std::size_t w = 4 + words_of(l).size();
      if (w <= max_column && w > column) column = w;
    }
    column += 2;
    std::string out;
    std::vector<std::string> bare;
    rows = 0;
    for (const auto &l : lines_) {
      bool annotate = annotated(l, rows);
      if (!annotate && bare.empty())
        out += "    // " + std::to_string(rows) + " rows above have comments; these have none.\n";
      if (l.what == kind::row) ++rows;
      if (!annotate) {
        auto ws = words_list(l);
        bare.insert(bare.end(), ws.begin(), ws.end());
        continue;
      }
      if (!bare.empty()) {
        out += fill(bare);
        bare.clear();
      }
      std::string ws = "    " + words_of(l);
      if (ws.size() <= max_column && column + 3 + l.note.size() <= limit) {
        out += ws + std::string(column - ws.size(), ' ') + "// " + l.note + "\n";
      } else {
        out += comment_lines(l.note);
        out += fill(words_list(l));
      }
    }
    if (!bare.empty()) out += fill(bare);
    return out;
  }

public:
  explicit writer(std::string prefix) : prefix_(std::move(prefix)) {}

  // Writes [root]: its nodes, then it.
  template <class T> void put_root(const T &root) {
    detail::walk_types<T>(types_);
    deps(root);
    while (!tasks_.empty()) {
      task &t = tasks_.back();
      if (written(t.type, t.key)) {
        tasks_.pop_back();
        continue;
      }
      if (!t.expanded) {
        t.expanded = true;
        std::function<void()> expand = t.expand;
        std::size_t mark = tasks_.size();
        expand();
        std::reverse(tasks_.begin() + mark, tasks_.end());
        continue;
      }
      std::function<void()> emit = std::move(t.emit);
      tasks_.pop_back();
      emit();
    }
    lines_.push_back({words_.size(), words_.size() + 1, node_count_ ? "end of the nodes" : "no nodes", kind::other});
    words_.push_back(0);
    lines_.push_back({words_.size(), 0, "the value: ", kind::other});
    put(root, lines_.back().note);
    end_row();
  }

  template <class T> void put(const T &x, std::string &note) {
    using namespace detail;
    if constexpr (std::is_enum_v<T>) {
      words_.push_back(to_word(x));
      std::string name = enumerator_name<T>(to_word(x));
      note += name.empty() ? std::to_string(to_word(x)) : name;
    } else if constexpr (std::is_arithmetic_v<T>) {
      words_.push_back(to_word(x));
      if constexpr (std::is_same_v<T, char>) {
        if (x >= 0x20 && x < 0x7f && x != '\'' && x != '\\') note += std::string("'") + x + "'";
        else note += scalar_literal(static_cast<int>(x));
      } else
        note += scalar_literal(x);
    } else if constexpr (string_like<T>) {
      put_text(x.data(), x.size(), note);
    } else if constexpr (pair_like<T>) {
      note += "{";
      put(x.first, note);
      note += ", ";
      put(x.second, note);
      note += "}";
    } else if constexpr (is_std_tuple<T>::value) {
      note += "{";
      std::size_t k = 0;
      std::apply([&](const auto &...e) { ((note += (k++ ? ", " : ""), put(e, note)), ...); }, x);
      note += "}";
    } else if constexpr (optional_like<T>) {
      words_.push_back(x.has_value());
      if (x.has_value()) put(*x, note);
      else note += "nullopt";
    } else if constexpr (handle<T>::value) {
      check_not_null(x);
      put(*x, note);
    } else if constexpr (is_list<T>::value) {
      std::size_t n = node_number(x);
      words_.push_back(n);
      note += "#" + std::to_string(n);
    } else if constexpr (is_shared_array<T>::value) {
      put_array(x, note);
    } else if constexpr (is_persistent_array<T>::value) {
      std::int64_t n = x.length();
      words_.push_back(static_cast<std::uint64_t>(n));
      note += "[default ";
      put(x.ref(n), note);  // out of bounds: the default element
      for (std::int64_t i = 0; i < n; ++i) {
        note += ", ";
        put(x.ref(i), note);
      }
      note += "]";
    } else if constexpr (inductive<T>) {
      if constexpr (is_node<T>()) {
        std::size_t n = node_number(x);
        words_.push_back(n);
        note += "#" + std::to_string(n);
      } else {
        using alts = typename alternatives<typename T::variant_t>::type;
        std::size_t i = x.v().index();
        words_.push_back(i);
        on_index(i, [&](auto ii) {
          note += last_component(type_name<std::tuple_element_t<decltype(ii)::value, alts>>());
        }, std::make_index_sequence<std::tuple_size_v<alts>>{});
      }
    } else if constexpr (std::is_empty_v<T>) {
      note += "{}";
    } else if constexpr (textual_number<T>) {
      std::string s = x.get_str(16);
      put_text(s.data(), s.size(), note);
    } else if constexpr (sequence<T>) {
      words_.push_back(x.size());
      note += "[";
      std::size_t k = 0;
      for (const auto &e : x) {
        note += k++ ? ", " : "";
        put(e, note);
      }
      note += "]";
    } else if constexpr (fielded<T>) {
      note += last_component(type_name<T>());
      put_fields(x, note);
    } else {
      static_assert(dependent_false<T>, "crane::bake: no way to write a value of this type");
    }
  }

  template <class E> void put_array(const crane::shared_array<E> &a, std::string &note) {
    if (a.empty()) {
      words_.push_back(0);
      note += "[]";
      return;
    }
    auto &s = arrays_[typeid(crane::shared_array<E>)];
    auto found = s.find(a.begin());
    // A static array is named by its block ([b3] for [<prefix>b3]), a heap
    // one by its place among the arrays written.
    if (found != s.end()) {
      words_.push_back(found->second + 3);
      if constexpr (detail::static_element<E>()) note += block_names_.at(a.begin()).substr(prefix_.size());
      else note += "array " + std::to_string(found->second) + " again";
      return;
    }
    s.emplace(a.begin(), s.size());
    if constexpr (detail::static_element<E>()) {
      std::string name = static_block(a);
      auto [it, fresh] = stream_block_index_.emplace(a.begin(), stream_blocks_.size());
      if (fresh) stream_blocks_.push_back(name);
      words_.push_back(2);
      words_.push_back(it->second);
      words_.push_back(detail::type_code<E>());
      note += name.substr(prefix_.size());
    } else {
      note += "array " + std::to_string(s.size() - 1) + " ";
      words_.push_back(1);
      words_.push_back(a.size());
      note += "[";
      std::size_t k = 0;
      for (const E &x : a) {
        note += k++ ? ", " : "";
        put(x, note);
      }
      note += "]";
    }
  }

  // The image as C++: the host's data model asserted, the static blocks, the
  // text, the stream and [symbol].
  std::string cpp(const std::string &symbol) const {
    char buf[32];
    std::string out = "// Baked by crane::bake: the value of " + symbol + ".\n";
    std::snprintf(buf, sizeof buf, "0x%" PRIx64 "u", data_model);
    out += "static_assert(crane::bake::data_model == " + std::string(buf) +
           ",\n              \"crane::bake: baked on a host with other scalar widths\");\n";
    out += decls_;
    std::string blocks = "nullptr", text = "nullptr";
    if (!stream_blocks_.empty()) {
      std::vector<std::string> bs;
      for (const auto &b : stream_blocks_) bs.push_back("&" + b);
      blocks = prefix_ + "blocks";
      out += declaration("constinit const void *const " + blocks + "[] = ", bs);
    }
    std::size_t text_chunks = 0;
    if (!text_.empty()) {
      text = prefix_ + "text";
      std::vector<std::string> chunks;
      text_chunks = (text_.size() + text_chunk - 1) / text_chunk;
      for (std::size_t c = 0; c < text_chunks; ++c) {
        std::string name = text + std::to_string(c);
        std::size_t size = std::min(text_chunk, text_.size() - c * text_chunk);
        out += text_declaration(name, c * text_chunk, c * text_chunk + size);
        chunks.push_back("std::string_view(" + name + ", " + std::to_string(size) + ")");
      }
      out += declaration("constinit const std::string_view " + text + "[] = ", chunks);
    }
    out += "constinit const std::uint64_t " + prefix_ + "words[] = {\n" + stream_lines() + "};\n";
    out += declaration("constinit const crane::bake::image " + symbol,
                       {prefix_ + "words", std::to_string(words_.size()), blocks,
                        std::to_string(stream_blocks_.size()), text, std::to_string(text_chunks)});
    return out;
  }
};

// Reads an image back.
class reader {
  const image &img_;
  std::size_t pos_ = 0;
  // Where the next string starts: a chunk of the text, and a place in it.
  std::size_t chunk_ = 0, chunk_pos_ = 0;
  // Per node type, numbered as [detail::walk_types] meets them, the function
  // that reads a run of its rows.
  struct types {
    std::unordered_map<std::type_index, std::size_t> ordinal;
    std::vector<void (reader::*)(std::size_t)> runs;
    template <class N> bool enter() {
      if (!ordinal.emplace(typeid(N), runs.size()).second) return false;
      runs.push_back(&reader::template run<N>);
      return true;
    }
  } types_;
  // Every node read, by number: the table holding it and its index there.
  std::vector<std::pair<const void *, std::size_t>> nodes_;
  // Per type: the nodes read, the counted pointers made to them (by node
  // number), the arrays read.
  std::unordered_map<std::type_index, std::shared_ptr<void>> tables_;

  template <class T> std::vector<T> &table() {
    auto &p = tables_[typeid(T)];
    if (!p) p = std::make_shared<std::vector<T>>();
    return *static_cast<std::vector<T> *>(p.get());
  }

  [[noreturn]] static void corrupt(const char *what) {
    std::fprintf(stderr, "crane::bake: the baked image does not match its type (%s)\n", what);
    std::abort();
  }

  std::uint64_t word() {
    if (pos_ >= img_.size) corrupt("too short");
    return img_.words[pos_++];
  }

  std::string get_text() {
    std::size_t n = word();
    std::string s;
    s.reserve(n);
    while (s.size() < n) {
      if (chunk_ >= img_.text_chunks) corrupt("a string");
      std::string_view c = img_.text[chunk_].substr(chunk_pos_);
      std::size_t take = std::min(c.size(), n - s.size());
      s.append(c.data(), take);
      chunk_pos_ += take;
      if (chunk_pos_ == img_.text[chunk_].size()) {
        ++chunk_;
        chunk_pos_ = 0;
      }
    }
    return s;
  }

  template <class A> A get_fields() {
    using F = detail::fields_t<A>;
    return [&]<std::size_t... K>(std::index_sequence<K...>) {
      return A{get<std::tuple_element_t<K, F>>()...};
    }(std::make_index_sequence<std::tuple_size_v<F>>{});
  }

  // The node the next word names, of type [T]; its number in [*number].
  template <class T> const T &node(std::size_t *number = nullptr) {
    std::uint64_t k = word();
    if (k >= nodes_.size()) corrupt("a node not yet read");
    auto &tab = table<T>();
    if (nodes_[k].first != &tab) corrupt("a node of another type");
    if (number) *number = k;
    return tab[nodes_[k].second];
  }

  void add_node(const void *tab, std::size_t index) { nodes_.emplace_back(tab, index); }

  // A run of [n] rows of the node type [T].  The table grows as a vector
  // does, not to the run's end: where node types alternate a run is one row
  // long, and reserving each run's rows would copy the table every row.
  template <class T> void run(std::size_t n) {
    auto &tab = table<T>();
    for (std::size_t r = 0; r < n; ++r) {
      std::uint64_t idx = word();
      if constexpr (detail::is_list<T>::value) {
        if (idx == 0) tab.emplace_back();
        else if (idx == 1) {
          auto h = get<typename T::value_type>();
          T tail = node<T>();
          tab.push_back(T::cons(std::move(h), std::move(tail)));
        } else
          corrupt("a list cell");
      } else {
        using alts = typename detail::alternatives<typename T::variant_t>::type;
        if (idx >= std::tuple_size_v<alts>) corrupt("a constructor index");
        detail::on_index(idx, [&](auto i) {
          using A = std::tuple_element_t<decltype(i)::value, alts>;
          if constexpr (std::is_empty_v<A>) tab.push_back(T(A{}));
          else tab.push_back(T(get_fields<A>()));
        }, std::make_index_sequence<std::tuple_size_v<alts>>{});
      }
      crane::make_immortal(tab.back());
      add_node(&tab, tab.size() - 1);
    }
  }

  template <class P> P get_handle() {
    using U = typename detail::handle<P>::element;
    if constexpr (detail::is_node<U>() && detail::handle<P>::counted) {
      // One pointer per node.
      std::size_t k;
      const U &u = node<U>(&k);
      auto &ptrs = table<std::optional<P>>();
      if (ptrs.size() <= k) ptrs.resize(nodes_.size());
      if (!ptrs[k]) ptrs[k] = detail::handle<P>::make(U(u));
      return *ptrs[k];
    } else
      return detail::handle<P>::make(get<U>());
  }

public:
  explicit reader(const image &img) : img_(img) {}
  bool done() const { return pos_ == img_.size && chunk_ == img_.text_chunks; }

  // The value of type [T]: its nodes, then it.
  template <class T> T get_root() {
    detail::walk_types<T>(types_);
    for (;;) {
      std::uint64_t t = word();
      if (t == 0) break;
      if (t - 1 >= types_.runs.size()) corrupt("a node type");
      std::size_t n = word();
      (this->*types_.runs[t - 1])(n);
    }
    return get<T>();
  }

  template <class T> T get() {
    using namespace detail;
    if constexpr (std::is_enum_v<T> || std::is_arithmetic_v<T>) {
      return of_word<T>(word());
    } else if constexpr (string_like<T>) {
      std::string s = get_text();
      return T(s.data(), s.size());
    } else if constexpr (pair_like<T>) {
      auto a = get<typename T::first_type>();
      auto b = get<typename T::second_type>();
      return T(std::move(a), std::move(b));
    } else if constexpr (is_std_tuple<T>::value) {
      return [&]<std::size_t... K>(std::index_sequence<K...>) {
        return T{get<std::tuple_element_t<K, T>>()...};
      }(std::make_index_sequence<std::tuple_size_v<T>>{});
    } else if constexpr (optional_like<T>) {
      if (!word()) return T{};
      return T(get<typename T::value_type>());
    } else if constexpr (handle<T>::value) {
      return get_handle<T>();
    } else if constexpr (is_list<T>::value) {
      return node<T>();
    } else if constexpr (is_shared_array<T>::value) {
      return get_array<typename T::value_type>();
    } else if constexpr (is_persistent_array<T>::value) {
      using E = typename is_persistent_array<T>::element;
      std::int64_t n = static_cast<std::int64_t>(word());
      E def = get<E>();
      T a(n, def);
      for (std::int64_t i = 0; i < n; ++i) a = std::move(a).set(i, get<E>());
      return a;
    } else if constexpr (inductive<T>) {
      if constexpr (is_node<T>()) return node<T>();
      else {
        using alts = typename alternatives<typename T::variant_t>::type;
        std::uint64_t idx = word();
        if (idx >= std::tuple_size_v<alts>) corrupt("a constructor index");
        std::optional<T> out;
        on_index(idx, [&](auto i) { out.emplace(std::tuple_element_t<decltype(i)::value, alts>{}); },
                 std::make_index_sequence<std::tuple_size_v<alts>>{});
        return std::move(*out);
      }
    } else if constexpr (std::is_empty_v<T>) {
      return T{};
    } else if constexpr (textual_number<T>) {
      return T(get_text(), 16);
    } else if constexpr (sequence<T>) {
      std::size_t n = word();
      T c;
      for (std::size_t i = 0; i < n; ++i) c.push_back(get<typename T::value_type>());
      return c;
    } else if constexpr (fielded<T>) {
      return get_fields<T>();
    } else {
      static_assert(dependent_false<T>, "crane::bake: no way to read a value of this type");
    }
  }

  template <class E> crane::shared_array<E> get_array() {
    std::uint64_t w = word();
    if (w == 0) return {};
    auto &tab = table<crane::shared_array<E>>();
    if (w >= 3) {
      if (w - 3 >= tab.size()) corrupt("a shared array");
      return tab[w - 3];
    }
    crane::shared_array<E> a;
    if (w == 2) {
      std::size_t b = word();
      if (b >= img_.block_count) corrupt("a static block");
      if constexpr (detail::static_element<E>()) {
        if (word() != detail::type_code<E>()) corrupt("a static block's element type");
        a = crane::shared_array<E>::adopt_static(img_.blocks[b]);
      } else
        corrupt("a static block of an element type with none");
    } else {
      std::size_t n = word();
      std::vector<E> elems;
      elems.reserve(n);
      for (std::size_t i = 0; i < n; ++i) elems.push_back(get<E>());
      a = crane::shared_array<E>::of_range(elems);
    }
    tab.push_back(a);
    return a;
  }
};

// The value of an image, at the type [T] of the declaration it initialises.
template <class T> T read(const image &img) {
  reader r(img);
  T v = r.template get_root<T>();
  crane::make_immortal(v);
  if (!r.done()) {
    std::fprintf(stderr, "crane::bake: the baked image does not match its type (too long)\n");
    std::abort();
  }
  return v;
}

// The value of an image, at the type it converts to: for a declaration whose
// type is not spelled.  A type with a converting constructor from anything
// ([std::optional]) takes the proxy as its payload rather than converting
// it, so a declaration that spells its type reads with [read<T>].
struct value {
  const image &img;
  template <class T> operator T() const { return read<T>(img); }
};

namespace detail {
inline std::function<std::string(const std::string &, const std::string &)> &root_writer() {
  static std::function<std::string(const std::string &, const std::string &)> f;
  return f;
}
} // namespace detail

// The bake target's initialiser, in the unit the driver links: the value,
// kept for [main] to write.
template <class T> T root(T v) {
  detail::root_writer() = [v](const std::string &symbol, const std::string &prefix) {
    writer w(prefix);
    w.put_root(v);
    return w.cpp(symbol);
  };
  return v;
}

// The bake driver: writes the root's image, declared as [argv[2]], with its
// static data's names starting with [argv[3]], to the file [argv[1]].
inline int main(int argc, char **argv) {
  if (argc != 4 || !detail::root_writer()) {
    std::fprintf(stderr, "crane::bake: usage: <out> <symbol> <prefix>, with a root\n");
    return 2;
  }
  std::string text = detail::root_writer()(argv[2], argv[3]);
  std::FILE *f = std::fopen(argv[1], "wb");
  if (!f) return 3;
  bool ok = std::fwrite(text.data(), 1, text.size(), f) == text.size();
  return std::fclose(f) == 0 && ok ? 0 : 3;
}

} // namespace crane::bake
