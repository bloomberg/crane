#include <generated_storage_field_name_clash.h>

bool GeneratedStorageFieldNameClash::is_flag(
    const GeneratedStorageFieldNameClash::d_v_ &x) {
  if (std::holds_alternative<
          typename GeneratedStorageFieldNameClash::d_v_::Empty>(x.v())) {
    return false;
  } else {
    const auto &[d_a0] =
        std::get<typename GeneratedStorageFieldNameClash::d_v_::Flag>(x.v());
    return d_a0;
  }
}
