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
// An image is a stream of 64-bit words and a table of static blocks.
//
// - A scalar (integer, character, boolean, enumeration, floating point) is
//   one word.  A [std::string] is its length and its bytes, eight to a word.
//   A pair, a tuple and an [std::optional] (a presence word first) are their
//   components in order; a type with no state is nothing.
// - A value of a generated inductive, record or flat struct starts with a
//   sharing word.  [k + 1] is the [k]th node already read, of this type: a
//   subterm shared in the value stays shared, so the value is read back as
//   the DAG it was.  0 is a new node: its constructor's index (0 for a record
//   or a flat struct) and its fields follow.  An enumeration is a new node
//   too, so it reads back as a nullary-constructor variant and back.  The
//   node a field points to through [std::shared_ptr], [crane::shared_box] or
//   [crane::rc] is written in place: the sharing is the inductive's.
// - A [crane::list] is its cells in order, each [1] and its head, ended by
//   [0] (nil) or [k + 2] (the tail is the [k]th cell already read).
// - A [crane::shared_array] is [0] (empty), [1] (its length and elements),
//   [k + 3] (the [k]th array already read) or [2] followed by a static block
//   and its element type's code: an array of scalars, or of such arrays,
//   whose block the image declares constant-initialised with an immortal
//   count ([crane::shared_array::fixed]), so it costs nothing at startup and
//   its count is never written.
//
// Reading builds the value once, at static initialisation, and makes every
// block it allocates immortal ([crane::make_immortal]): the value lives as
// long as the program, and reading it from any thread never touches its
// counts.
//
// The format is the same on every byte order: a word is written as the
// number it is, never as memory, and a string's bytes are packed by shifts.
// What it does assume is asserted below; and an image asserts that the
// target reads its scalars at the widths the bake host wrote them at
// ([data_model]), which is what cross-compiling a baked unit could break.

#pragma once

#include <bit>
#include <cinttypes>
#include <climits>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <type_traits>
#include <typeindex>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

#include "conslist.h"
#include "shared_array.h"
#include "shared_variant.h"

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
};

// The widths of the scalar types an image may hold, which the bake host and
// the target must agree on: each image asserts it equals the host's.
inline constexpr std::uint64_t data_model =
    std::uint64_t(sizeof(short)) | std::uint64_t(sizeof(int)) << 8 | std::uint64_t(sizeof(long)) << 16 |
    std::uint64_t(sizeof(long long)) << 24 | std::uint64_t(sizeof(wchar_t)) << 32 |
    std::uint64_t(sizeof(std::size_t)) << 40;


namespace detail {

template <class T> struct is_std_pair : std::false_type {};
template <class A, class B> struct is_std_pair<std::pair<A, B>> : std::true_type {};
template <class T> struct is_std_tuple : std::false_type {};
template <class... A> struct is_std_tuple<std::tuple<A...>> : std::true_type {};
template <class T> struct is_std_optional : std::false_type {};
template <class A> struct is_std_optional<std::optional<A>> : std::true_type {};
template <class T> struct is_std_shared_ptr : std::false_type {};
template <class A> struct is_std_shared_ptr<std::shared_ptr<A>> : std::true_type {};
template <class T> struct is_shared_box : std::false_type {};
template <class A> struct is_shared_box<crane::shared_box<A>> : std::true_type {};
template <class T> struct is_rc : std::false_type {};
template <class A> struct is_rc<crane::rc<A>> : std::true_type {};
template <class T> struct is_list : std::false_type {};
template <class A> struct is_list<crane::list<A>> : std::true_type {};
template <class T> struct is_shared_array : std::false_type {};
template <class A> struct is_shared_array<crane::shared_array<A>> : std::true_type {};

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

template <class A> auto field_types(A &a) {
  auto &[... fs] = a;
  return std::type_identity<std::tuple<std::remove_cvref_t<decltype(fs)>...>>{};
}
template <class A> using fields_t = typename decltype(field_types(std::declval<A &>()))::type;

template <class A, class F> void each(const A &a, F &&f) {
  const auto &[... fs] = a;
  (f(fs), ...);
}

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

template <class T> std::uint64_t to_word(T x) {
  if constexpr (std::is_enum_v<T>) return static_cast<std::uint64_t>(static_cast<std::underlying_type_t<T>>(x));
  else if constexpr (std::is_same_v<T, float>) return std::bit_cast<std::uint32_t>(x);
  else if constexpr (std::is_same_v<T, double>) return std::bit_cast<std::uint64_t>(x);
  else if constexpr (std::is_signed_v<T>) return static_cast<std::uint64_t>(static_cast<std::int64_t>(x));
  else return static_cast<std::uint64_t>(x);
}

template <class T> T of_word(std::uint64_t w) {
  if constexpr (std::is_enum_v<T>) return static_cast<T>(static_cast<std::underlying_type_t<T>>(w));
  else if constexpr (std::is_same_v<T, float>) return std::bit_cast<float>(static_cast<std::uint32_t>(w));
  else if constexpr (std::is_same_v<T, double>) return std::bit_cast<double>(w);
  else if constexpr (std::is_signed_v<T>) return static_cast<T>(static_cast<std::int64_t>(w));
  else return static_cast<T>(w);
}

template <class T> constexpr bool dependent_false = false;

} // namespace detail

// Writes a value as an image (the bake driver's side).
class writer {
  std::vector<std::uint64_t> words_;
  // Per type, the nodes written so far, by address.
  std::unordered_map<std::type_index, std::unordered_map<const void *, std::size_t>> seen_;
  // Static blocks: their declarations, by address; the ones the stream names.
  std::string decls_;
  std::unordered_map<const void *, std::string> block_names_;
  std::vector<std::string> stream_blocks_;
  std::unordered_map<const void *, std::size_t> stream_block_index_;
  std::string prefix_;

  template <class T> std::unordered_map<const void *, std::size_t> &seen() { return seen_[typeid(T)]; }

  // A node of type T at [addr]: its sharing word, true if it is new.
  template <class T> bool node(const void *addr) {
    auto &s = seen<T>();
    if (addr) {
      auto it = s.find(addr);
      if (it != s.end()) {
        words_.push_back(it->second + 1);
        return false;
      }
      s.emplace(addr, s.size());
    }
    words_.push_back(0);
    return true;
  }

  template <class E> static std::string literal(const E &x) {
    char buf[64];
    if constexpr (std::is_same_v<E, bool>) return x ? "true" : "false";
    else if constexpr (std::is_floating_point_v<E>) std::snprintf(buf, sizeof buf, "%a", static_cast<double>(x));
    else if constexpr (std::is_signed_v<E>) {
      long long v = x;
      if (v == std::numeric_limits<long long>::min()) return "(-9223372036854775807LL - 1)";
      std::snprintf(buf, sizeof buf, "%lldLL", v);
    } else
      std::snprintf(buf, sizeof buf, "%lluULL", static_cast<unsigned long long>(x));
    return buf;
  }

  template <class E> static std::string type_name() {
    if constexpr (detail::is_shared_array<E>::value)
      return "crane::shared_array<" + type_name<typename E::value_type>() + ">";
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
        if (x.empty()) elems.push_back("crane::shared_array<" + type_name<typename E::value_type>() + ">{}");
        else elems.push_back(type_name<E>() + "::of_static(" + static_block(x) + ")");
      } else
        elems.push_back(literal(x));
    }
    std::string name = prefix_ + "b" + std::to_string(block_names_.size());
    decls_ += declaration("[[clang::no_destroy]] constinit " + type_name<crane::shared_array<E>>() + "::fixed<" +
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
  // own: one per word of the stream.
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

public:
  explicit writer(std::string prefix) : prefix_(std::move(prefix)) {}

  template <class T> void put(const T &x) {
    using namespace detail;
    if constexpr (std::is_enum_v<T>) {
      words_.push_back(0);
      words_.push_back(to_word(x));
    } else if constexpr (std::is_arithmetic_v<T>) {
      words_.push_back(to_word(x));
    } else if constexpr (std::is_same_v<T, std::string>) {
      words_.push_back(x.size());
      for (std::size_t i = 0; i < x.size(); i += 8) {
        std::uint64_t w = 0;
        for (std::size_t j = 0; j < 8 && i + j < x.size(); ++j)
          w |= std::uint64_t(static_cast<unsigned char>(x[i + j])) << (8 * j);
        words_.push_back(w);
      }
    } else if constexpr (is_std_pair<T>::value) {
      put(x.first);
      put(x.second);
    } else if constexpr (is_std_tuple<T>::value) {
      std::apply([&](const auto &...e) { (put(e), ...); }, x);
    } else if constexpr (is_std_optional<T>::value) {
      words_.push_back(x.has_value());
      if (x) put(*x);
    } else if constexpr (is_std_shared_ptr<T>::value || is_shared_box<T>::value || is_rc<T>::value) {
      if (!x) {
        std::fprintf(stderr, "crane::bake: a null pointer in the value\n");
        std::exit(2);
      }
      put(*x);
    } else if constexpr (is_list<T>::value) {
      put_list(x);
    } else if constexpr (is_shared_array<T>::value) {
      put_array(x);
    } else if constexpr (inductive<T>) {
      using V = typename T::variant_t;
      using alts = typename alternatives<V>::type;
      const V &v = x.v();
      on_index(v.index(), [&](auto i) {
        constexpr std::size_t I = decltype(i)::value;
        using A = std::tuple_element_t<I, alts>;
        const A &a = alt_at<I>(v);
        if (!node<T>(std::is_empty_v<A> ? nullptr : static_cast<const void *>(&a))) return;
        words_.push_back(I);
        if constexpr (!std::is_empty_v<A>) each(a, [&](const auto &f) { put(f); });
      }, std::make_index_sequence<std::tuple_size_v<alts>>{});
    } else if constexpr (std::is_empty_v<T>) {
    } else if constexpr (fielded<T>) {
      words_.push_back(0);
      words_.push_back(0);
      each(x, [&](const auto &f) { put(f); });
    } else {
      static_assert(dependent_false<T>, "crane::bake: no way to write a value of this type");
    }
  }

  template <class E> void put_list(const crane::list<E> &l) {
    auto &s = seen<crane::list<E>>();
    for (auto it = l.begin(); it != l.end(); ++it) {
      const void *cell = &*it;
      auto found = s.find(cell);
      if (found != s.end()) {
        words_.push_back(found->second + 2);
        return;
      }
      s.emplace(cell, s.size());
      words_.push_back(1);
      put(*it);
    }
    words_.push_back(0);
  }

  template <class E> void put_array(const crane::shared_array<E> &a) {
    if (a.empty()) {
      words_.push_back(0);
      return;
    }
    auto &s = seen<crane::shared_array<E>>();
    auto found = s.find(a.begin());
    if (found != s.end()) {
      words_.push_back(found->second + 3);
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
    } else {
      words_.push_back(1);
      words_.push_back(a.size());
      for (const E &x : a) put(x);
    }
  }

  // The image as C++: the host's data model asserted, the static blocks, the
  // stream and [symbol], laid out as Crane lays out the code around it.
  std::string cpp(const std::string &symbol) const {
    char buf[32];
    std::string out = "// Baked by crane::bake: the value of " + symbol + ".\n";
    std::snprintf(buf, sizeof buf, "0x%" PRIx64 "u", data_model);
    out += "static_assert(crane::bake::data_model == " + std::string(buf) +
           ",\n              \"crane::bake: baked on a host with other scalar widths\");\n";
    out += decls_;
    std::vector<std::string> blocks;
    for (const auto &b : stream_blocks_) blocks.push_back("&" + b);
    if (blocks.empty()) blocks.push_back("nullptr");
    out += declaration("constinit const void *const " + prefix_ + "blocks[] = ", blocks);
    std::vector<std::string> words;
    words.reserve(words_.size());
    for (std::uint64_t w : words_) {
      std::snprintf(buf, sizeof buf, "0x%" PRIx64 "u", w);
      words.push_back(buf);
    }
    out += declaration("constinit const std::uint64_t " + prefix_ + "words[] = ", words);
    out += declaration("constinit const crane::bake::image " + symbol,
                       {prefix_ + "words", std::to_string(words_.size()), prefix_ + "blocks",
                        std::to_string(stream_blocks_.size())});
    return out;
  }
};

// Reads an image back.
class reader {
  const image &img_;
  std::size_t pos_ = 0;
  std::unordered_map<std::type_index, std::shared_ptr<void>> tables_;

  template <class T> std::vector<std::optional<T>> &table() {
    auto &p = tables_[typeid(T)];
    if (!p) p = std::make_shared<std::vector<std::optional<T>>>();
    return *static_cast<std::vector<std::optional<T>> *>(p.get());
  }

  [[noreturn]] static void corrupt(const char *what) {
    std::fprintf(stderr, "crane::bake: the baked image does not match its type (%s)\n", what);
    std::abort();
  }

  std::uint64_t word() {
    if (pos_ >= img_.size) corrupt("too short");
    return img_.words[pos_++];
  }

  template <class A> A get_fields() {
    using F = detail::fields_t<A>;
    return [&]<std::size_t... K>(std::index_sequence<K...>) {
      return A{get<std::tuple_element_t<K, F>>()...};
    }(std::make_index_sequence<std::tuple_size_v<F>>{});
  }

  // A pointer to a node: the node read in place, and the pointer made for
  // it kept by the node's index, so a node shared in the value is pointed
  // to by one pointer again rather than copied into a second one.
  template <class P, class Make> P get_pointer(Make &&make) {
    using U = typename P::element_type;
    if constexpr (detail::inductive<U>) {
      auto &ptrs = table<P>();
      if (pos_ >= img_.size) corrupt("too short");
      std::uint64_t share = img_.words[pos_];
      if (share != 0 && share - 1 < ptrs.size() && ptrs[share - 1]) {
        ++pos_;
        return *ptrs[share - 1];
      }
      std::size_t id = table<U>().size();
      P p = make(get<U>());
      if (share == 0 && table<U>().size() > id) {
        if (ptrs.size() <= id) ptrs.resize(id + 1);
        ptrs[id] = p;
      }
      return p;
    } else
      return make(get<U>());
  }

public:
  explicit reader(const image &img) : img_(img) {}
  bool done() const { return pos_ == img_.size; }

  template <class T> T get() {
    using namespace detail;
    if constexpr (std::is_enum_v<T>) {
      if (word() != 0) corrupt("an enumeration shared");
      return of_word<T>(word());
    } else if constexpr (std::is_arithmetic_v<T>) {
      return of_word<T>(word());
    } else if constexpr (std::is_same_v<T, std::string>) {
      std::size_t n = word();
      std::string s(n, '\0');
      for (std::size_t i = 0; i < n; i += 8) {
        std::uint64_t w = word();
        for (std::size_t j = 0; j < 8 && i + j < n; ++j) s[i + j] = static_cast<char>((w >> (8 * j)) & 0xff);
      }
      return s;
    } else if constexpr (is_std_pair<T>::value) {
      auto a = get<typename T::first_type>();
      auto b = get<typename T::second_type>();
      return T(std::move(a), std::move(b));
    } else if constexpr (is_std_tuple<T>::value) {
      return [&]<std::size_t... K>(std::index_sequence<K...>) {
        return T{get<std::tuple_element_t<K, T>>()...};
      }(std::make_index_sequence<std::tuple_size_v<T>>{});
    } else if constexpr (is_std_optional<T>::value) {
      if (!word()) return T{};
      return T(get<typename T::value_type>());
    } else if constexpr (is_std_shared_ptr<T>::value) {
      return get_pointer<T>([](auto &&u) { return std::make_shared<typename T::element_type>(std::move(u)); });
    } else if constexpr (is_shared_box<T>::value) {
      return T::make(get<typename T::element_type>());
    } else if constexpr (is_rc<T>::value) {
      return get_pointer<T>([](auto &&u) { return crane::make_rc<typename T::element_type>(std::move(u)); });
    } else if constexpr (is_list<T>::value) {
      return get_list<typename T::value_type>();
    } else if constexpr (is_shared_array<T>::value) {
      return get_array<typename T::value_type>();
    } else if constexpr (inductive<T>) {
      using V = typename T::variant_t;
      using alts = typename alternatives<V>::type;
      auto &tab = table<T>();
      std::uint64_t share = word();
      if (share != 0) {
        if (share - 1 >= tab.size() || !tab[share - 1]) corrupt("a shared node");
        return *tab[share - 1];
      }
      std::size_t idx = word();
      if (idx >= std::tuple_size_v<alts>) corrupt("a constructor index");
      std::optional<T> out;
      on_index(idx, [&](auto i) {
        constexpr std::size_t I = decltype(i)::value;
        using A = std::tuple_element_t<I, alts>;
        if constexpr (std::is_empty_v<A>) {
          out.emplace(A{});
        } else {
          std::size_t id = tab.size();
          tab.emplace_back();
          T t(get_fields<A>());
          crane::make_immortal(t);
          table<T>()[id] = t;
          out.emplace(std::move(t));
        }
      }, std::make_index_sequence<std::tuple_size_v<alts>>{});
      return std::move(*out);
    } else if constexpr (std::is_empty_v<T>) {
      return T{};
    } else if constexpr (fielded<T>) {
      if (word() != 0 || word() != 0) corrupt("a record");
      return get_fields<T>();
    } else {
      static_assert(dependent_false<T>, "crane::bake: no way to read a value of this type");
    }
  }

  template <class E> crane::list<E> get_list() {
    auto &tab = table<crane::list<E>>();
    std::vector<std::pair<std::size_t, E>> heads;
    crane::list<E> rest;
    for (;;) {
      std::uint64_t w = word();
      if (w == 0) break;
      if (w >= 2) {
        if (w - 2 >= tab.size() || !tab[w - 2]) corrupt("a shared list");
        rest = *tab[w - 2];
        break;
      }
      std::size_t id = tab.size();
      tab.emplace_back();
      E h = get<E>();
      heads.emplace_back(id, std::move(h));
    }
    for (std::size_t k = heads.size(); k > 0; --k) {
      rest = crane::list<E>::cons(std::move(heads[k - 1].second), std::move(rest));
      table<crane::list<E>>()[heads[k - 1].first] = rest;
    }
    return rest;
  }

  template <class E> crane::shared_array<E> get_array() {
    std::uint64_t w = word();
    if (w == 0) return {};
    auto &tab = table<crane::shared_array<E>>();
    if (w >= 3) {
      if (w - 3 >= tab.size() || !tab[w - 3]) corrupt("a shared array");
      return *tab[w - 3];
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
    tab.emplace_back(a);
    return a;
  }
};

// The value of an image, at the type [T] of the declaration it initialises.
template <class T> T read(const image &img) {
  reader r(img);
  T v = r.template get<T>();
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
    w.put(v);
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
