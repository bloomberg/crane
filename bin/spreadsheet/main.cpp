// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Crane spreadsheet front-end.  Owns a single [Spreadsheet::Sheet] and
// drives it through a Dear ImGui table.  All evaluation is delegated to
// the Crane-extracted [Spreadsheet] module.

#include "Spreadsheet.h"
#include "formula.h"

#include <imgui.h>
#include <imgui_impl_glfw.h>
#include <imgui_impl_opengl3.h>

#include <GLFW/glfw3.h>

#include <array>
#include <cstdio>
#include <cstring>
#include <deque>
#include <fstream>
#include <optional>
#include <sstream>
#include <string>
#include <vector>

namespace {

const int NUM_COLS = static_cast<int>(Spreadsheet::NUM_COLS);
const int NUM_ROWS = static_cast<int>(Spreadsheet::NUM_ROWS);
constexpr int UNDO_CAP = 64;

// Per-cell editing state.  Holds the source string the user is typing
// (independent of the kernel's evaluated value), plus a flag that records
// whether the last commit failed to parse.
struct EditBuf {
  std::array<char, 128> buf{};
  bool parse_error = false;
};

// Right-aligned, width-truncated draw of [text] inside the current
// table cell's avail area.
void draw_cell_text(const char* text, ImU32 col, bool right_align) {
  ImVec2 avail = ImGui::GetContentRegionAvail();
  ImVec2 cursor = ImGui::GetCursorScreenPos();
  ImDrawList* dl = ImGui::GetWindowDrawList();
  ImFont* font = ImGui::GetFont();
  float font_size = ImGui::GetFontSize();

  // Find the longest prefix that fits.  Walk back from the full string.
  std::string s(text);
  float w = ImGui::CalcTextSize(s.c_str()).x;
  if (w > avail.x && !s.empty()) {
    // Replace the tail with '~' until it fits.
    while (!s.empty() && ImGui::CalcTextSize((s + "~").c_str()).x > avail.x) {
      s.pop_back();
    }
    s += "~";
  }
  ImVec2 sz = ImGui::CalcTextSize(s.c_str());
  float x_off = right_align ? std::max(0.0f, avail.x - sz.x) : 0.0f;
  ImVec2 pos = {cursor.x + x_off, cursor.y};
  dl->AddText(font, font_size, pos, col, s.c_str());
  // Reserve the row height so the table layout doesn't collapse.
  ImGui::Dummy({avail.x, sz.y});
}

bool is_numeric_display(const std::string& s) {
  size_t i = 0;
  if (i < s.size() && (s[i] == '-' || s[i] == '+')) ++i;
  if (i >= s.size()) return false;
  for (; i < s.size(); ++i) {
    if (!std::isdigit(static_cast<unsigned char>(s[i]))) return false;
  }
  return true;
}

class App {
 public:
  App() : sheet_(Spreadsheet::new_sheet) {
    edits_.resize(static_cast<size_t>(NUM_COLS) * NUM_ROWS);
  }

  void render() {
    handle_shortcuts();

    if (ImGui::Begin("Crane Spreadsheet", nullptr, ImGuiWindowFlags_MenuBar)) {
      menu_bar();
      formula_bar();
      ImGui::Separator();

      static const ImGuiTableFlags table_flags =
          ImGuiTableFlags_Resizable | ImGuiTableFlags_Borders |
          ImGuiTableFlags_RowBg | ImGuiTableFlags_ScrollX |
          ImGuiTableFlags_ScrollY | ImGuiTableFlags_SizingFixedFit;

      ImVec2 outer = ImGui::GetContentRegionAvail();
      if (ImGui::BeginTable("grid", NUM_COLS + 1, table_flags, outer)) {
        ImGui::TableSetupScrollFreeze(1, 1);
        ImGui::TableSetupColumn("",
            ImGuiTableColumnFlags_WidthFixed | ImGuiTableColumnFlags_NoHide,
            32.0f);
        for (int c = 0; c < NUM_COLS; ++c) {
          std::string label = formula::col_label(c);
          ImGui::TableSetupColumn(label.c_str(),
              ImGuiTableColumnFlags_WidthFixed, 80.0f);
        }
        ImGui::TableHeadersRow();

        ImGuiListClipper clipper;
        clipper.Begin(NUM_ROWS);
        while (clipper.Step()) {
          for (int r = clipper.DisplayStart; r < clipper.DisplayEnd; ++r) {
            ImGui::TableNextRow();
            ImGui::TableSetColumnIndex(0);
            ImGui::Text("%d", r + 1);
            for (int c = 0; c < NUM_COLS; ++c) {
              ImGui::TableSetColumnIndex(c + 1);
              cell_widget(c, r);
            }
          }
        }
        ImGui::EndTable();
      }
    }
    ImGui::End();

    about_modal();
  }

 private:
  void menu_bar() {
    if (ImGui::BeginMenuBar()) {
      if (ImGui::BeginMenu("File")) {
        if (ImGui::MenuItem("New", "Ctrl+N")) clear_sheet();
        if (ImGui::MenuItem("Open...", "Ctrl+O")) load_from("spreadsheet.txt");
        if (ImGui::MenuItem("Save", "Ctrl+S")) save_to("spreadsheet.txt");
        ImGui::EndMenu();
      }
      if (ImGui::BeginMenu("Edit")) {
        if (ImGui::MenuItem("Undo", "Ctrl+Z", false, !undo_.empty())) do_undo();
        if (ImGui::MenuItem("Redo", "Ctrl+Y", false, !redo_.empty())) do_redo();
        ImGui::Separator();
        if (ImGui::MenuItem("Copy", "Ctrl+C", false, has_selection())) do_copy();
        if (ImGui::MenuItem("Paste", "Ctrl+V", false, has_clip())) do_paste();
        ImGui::EndMenu();
      }
      if (ImGui::BeginMenu("Help")) {
        if (ImGui::MenuItem("About...")) show_about_ = true;
        ImGui::EndMenu();
      }
      ImGui::EndMenuBar();
    }
  }

  void formula_bar() {
    char ref_label[16] = "";
    if (selected_ >= 0) {
      auto lab = formula::label_of(selected_col(), selected_row());
      std::strncpy(ref_label, lab.c_str(), sizeof(ref_label) - 1);
    }
    ImGui::SetNextItemWidth(80.0f);
    ImGui::InputText("##ref", ref_label, sizeof(ref_label),
                     ImGuiInputTextFlags_ReadOnly);
    ImGui::SameLine();
    ImGui::SetNextItemWidth(-FLT_MIN);
    if (selected_ >= 0) {
      EditBuf& eb = edits_[selected_];
      if (ImGui::InputText("##fbar", eb.buf.data(), eb.buf.size(),
                           ImGuiInputTextFlags_EnterReturnsTrue)) {
        commit(selected_col(), selected_row());
      }
    } else {
      char empty[1] = "";
      ImGui::InputText("##fbar", empty, sizeof(empty),
                       ImGuiInputTextFlags_ReadOnly);
    }
  }

  void about_modal() {
    if (show_about_) {
      ImGui::OpenPopup("About Crane Spreadsheet");
      show_about_ = false;
    }
    ImVec2 center = ImGui::GetMainViewport()->GetCenter();
    ImGui::SetNextWindowPos(center, ImGuiCond_Appearing, {0.5f, 0.5f});
    if (ImGui::BeginPopupModal("About Crane Spreadsheet", nullptr,
                                ImGuiWindowFlags_AlwaysAutoResize)) {
      ImGui::TextUnformatted("Crane Spreadsheet");
      ImGui::Spacing();
      ImGui::TextUnformatted(
          "A small spreadsheet driven by a Rocq-extracted kernel.\n\n"
          "Click a cell to select; double-click to edit.\n"
          "Type a number for a literal, =A1+B2 for a formula.\n"
          "Operators: + - * /, parentheses, A..CZ refs.\n\n"
          "Errors:\n"
          "  #PARSE  - the formula didn't parse.\n"
          "  #ERR    - cycle, divide-by-zero, or out of fuel.");
      ImGui::Spacing();
      if (ImGui::Button("OK", {120, 0})) ImGui::CloseCurrentPopup();
      ImGui::EndPopup();
    }
  }

  size_t idx(int c, int r) const {
    return static_cast<size_t>(r) * NUM_COLS + c;
  }
  int selected_col() const { return selected_ % NUM_COLS; }
  int selected_row() const { return selected_ / NUM_COLS; }

  void cell_widget(int c, int r) {
    EditBuf& eb = edits_[idx(c, r)];
    int my_idx = static_cast<int>(idx(c, r));
    bool is_editing = (editing_ == my_idx);

    ImGui::PushID(my_idx);
    ImGui::SetNextItemWidth(-FLT_MIN);

    if (is_editing) {
      if (just_started_editing_) {
        ImGui::SetKeyboardFocusHere();
        just_started_editing_ = false;
      }
      if (ImGui::InputText("##cell", eb.buf.data(), eb.buf.size(),
                           ImGuiInputTextFlags_EnterReturnsTrue |
                           ImGuiInputTextFlags_AutoSelectAll)) {
        commit(c, r);
        editing_ = -1;
      }
      // If focus moves elsewhere, commit and exit edit mode.
      if (editing_ == my_idx && !ImGui::IsItemActive() &&
          !ImGui::IsItemFocused() && !just_started_editing_) {
        commit(c, r);
        editing_ = -1;
      }
    } else {
      auto display = display_for(c, r, eb);
      bool is_selected = (selected_ == my_idx);

      ImGuiSelectableFlags flags = ImGuiSelectableFlags_AllowDoubleClick |
                                   ImGuiSelectableFlags_AllowOverlap;
      // Use a transparent selectable as the hit target, then overlay the
      // cell text with our own positioning so we can right-align numbers
      // and truncate cleanly.
      ImVec2 cell_size = {ImGui::GetContentRegionAvail().x,
                          ImGui::GetTextLineHeightWithSpacing()};
      ImVec2 start = ImGui::GetCursorScreenPos();
      if (ImGui::Selectable("##sel", is_selected, flags, cell_size)) {
        selected_ = my_idx;
        if (ImGui::IsMouseDoubleClicked(ImGuiMouseButton_Left)) {
          start_editing(c, r);
        }
      }
      ImGui::SetCursorScreenPos(start);

      if (display) {
        ImU32 col = ImGui::GetColorU32(ImGuiCol_Text);
        bool err = eb.parse_error || (display->size() >= 1 &&
                                       display->front() == '#');
        if (err) col = IM_COL32(220, 80, 80, 255);
        bool right_align = !err && is_numeric_display(*display);
        draw_cell_text(display->c_str(), col, right_align);
      } else {
        ImGui::Dummy(cell_size);
      }
    }
    ImGui::PopID();
  }

  std::optional<std::string> display_for(int c, int r, const EditBuf& eb) {
    if (eb.parse_error) return std::string("#PARSE");
    Spreadsheet::CellRef ref{static_cast<int64_t>(c), static_cast<int64_t>(r)};
    auto cell = Spreadsheet::get_cell(sheet_, ref);
    if (std::holds_alternative<Spreadsheet::Cell::CEmpty>(cell.v())) {
      return std::nullopt;
    }
    auto val = Spreadsheet::eval_cell(Spreadsheet::DEFAULT_FUEL, sheet_, ref);
    if (!val) return std::string("#ERR");
    return std::to_string(*val);
  }

  void start_editing(int c, int r) {
    editing_ = static_cast<int>(idx(c, r));
    just_started_editing_ = true;
    selected_ = editing_;
  }

  void commit(int c, int r) {
    EditBuf& eb = edits_[idx(c, r)];
    Spreadsheet::CellRef ref{static_cast<int64_t>(c), static_cast<int64_t>(r)};
    std::string_view src(eb.buf.data());
    while (!src.empty() && std::isspace(static_cast<unsigned char>(src.front())))
      src.remove_prefix(1);

    Spreadsheet::Sheet before = sheet_;
    bool changed = false;

    if (src.empty()) {
      sheet_ = Spreadsheet::set_cell(sheet_, ref, Spreadsheet::Cell::cempty());
      eb.parse_error = false;
      changed = true;
    } else if (src.front() == '=') {
      auto e = formula::parse(src.substr(1));
      if (!e) {
        eb.parse_error = true;
      } else {
        sheet_ = Spreadsheet::set_cell(sheet_, ref,
            Spreadsheet::Cell::cform(std::move(*e)));
        eb.parse_error = false;
        changed = true;
      }
    } else {
      int64_t v;
      if (formula::parse_int_literal(src, v)) {
        sheet_ = Spreadsheet::set_cell(sheet_, ref, Spreadsheet::Cell::clit(v));
        eb.parse_error = false;
        changed = true;
      } else {
        eb.parse_error = true;
      }
    }

    if (changed) push_undo(std::move(before));
  }

  void clear_sheet() {
    push_undo(std::move(sheet_));
    sheet_ = Spreadsheet::new_sheet;
    for (auto& e : edits_) {
      e.buf[0] = '\0';
      e.parse_error = false;
    }
  }

  // --- Selection / clipboard ----------------------------------------------

  bool has_selection() const { return selected_ >= 0; }
  bool has_clip() const { return !clipboard_.empty(); }

  void do_copy() {
    if (!has_selection()) return;
    clipboard_ = edits_[selected_].buf.data();
    if (clipboard_.empty()) {
      // For an empty edit buffer but non-empty cell, regenerate text.
      Spreadsheet::CellRef ref{selected_col(), selected_row()};
      auto cell = Spreadsheet::get_cell(sheet_, ref);
      if (std::holds_alternative<Spreadsheet::Cell::CLit>(cell.v())) {
        const auto& [v] = std::get<Spreadsheet::Cell::CLit>(cell.v());
        clipboard_ = std::to_string(v);
      }
      // Formulas: source isn't reconstructible from the AST without a
      // pretty-printer.  We leave that for a future iteration.
    }
    ImGui::SetClipboardText(clipboard_.c_str());
  }

  void do_paste() {
    if (!has_selection()) return;
    // Prefer OS clipboard if it has text; otherwise our local copy.
    const char* os = ImGui::GetClipboardText();
    std::string text = (os && *os) ? std::string(os) : clipboard_;
    EditBuf& eb = edits_[selected_];
    std::strncpy(eb.buf.data(), text.c_str(), eb.buf.size() - 1);
    eb.buf[eb.buf.size() - 1] = '\0';
    commit(selected_col(), selected_row());
  }

  // --- Undo/redo ----------------------------------------------------------

  void push_undo(Spreadsheet::Sheet before) {
    undo_.push_back(std::move(before));
    if (static_cast<int>(undo_.size()) > UNDO_CAP) undo_.pop_front();
    redo_.clear();
  }
  void do_undo() {
    if (undo_.empty()) return;
    redo_.push_back(std::move(sheet_));
    sheet_ = std::move(undo_.back());
    undo_.pop_back();
  }
  void do_redo() {
    if (redo_.empty()) return;
    undo_.push_back(std::move(sheet_));
    sheet_ = std::move(redo_.back());
    redo_.pop_back();
  }

  // --- Save/load ----------------------------------------------------------

  // Format: one entry per line:
  //   col,row,source
  // where source is the raw string the user typed (literal or =formula).
  // Lines starting with # are comments.  We dump only non-empty edit
  // buffers; the underlying AST isn't pretty-printable yet, so cells
  // entered via paste-without-text are lost on save.
  void save_to(const std::string& path) {
    std::ofstream f(path);
    if (!f) return;
    f << "# Crane spreadsheet\n";
    for (int r = 0; r < NUM_ROWS; ++r) {
      for (int c = 0; c < NUM_COLS; ++c) {
        const EditBuf& eb = edits_[idx(c, r)];
        if (eb.buf[0] == '\0') continue;
        f << c << "," << r << "," << eb.buf.data() << "\n";
      }
    }
  }
  void load_from(const std::string& path) {
    std::ifstream f(path);
    if (!f) return;
    push_undo(std::move(sheet_));
    sheet_ = Spreadsheet::new_sheet;
    for (auto& e : edits_) {
      e.buf[0] = '\0';
      e.parse_error = false;
    }
    std::string line;
    while (std::getline(f, line)) {
      if (line.empty() || line.front() == '#') continue;
      size_t p1 = line.find(',');
      size_t p2 = (p1 == std::string::npos) ? std::string::npos
                                            : line.find(',', p1 + 1);
      if (p2 == std::string::npos) continue;
      int c = std::atoi(line.substr(0, p1).c_str());
      int r = std::atoi(line.substr(p1 + 1, p2 - p1 - 1).c_str());
      std::string src = line.substr(p2 + 1);
      if (c < 0 || c >= NUM_COLS || r < 0 || r >= NUM_ROWS) continue;
      EditBuf& eb = edits_[idx(c, r)];
      std::strncpy(eb.buf.data(), src.c_str(), eb.buf.size() - 1);
      eb.buf[eb.buf.size() - 1] = '\0';
      // Recommit so the kernel state matches.
      commit(c, r);
    }
    // The commits above pushed undos; collapse them so a single Undo
    // reverts the whole load.
    if (undo_.size() > 1) {
      auto first = std::move(undo_.front());
      undo_.clear();
      undo_.push_back(std::move(first));
    }
  }

  // --- Keyboard shortcuts -------------------------------------------------

  void handle_shortcuts() {
    ImGuiIO& io = ImGui::GetIO();
    if (io.KeyCtrl) {
      if (ImGui::IsKeyPressed(ImGuiKey_Z)) do_undo();
      else if (ImGui::IsKeyPressed(ImGuiKey_Y)) do_redo();
      else if (ImGui::IsKeyPressed(ImGuiKey_C)) do_copy();
      else if (ImGui::IsKeyPressed(ImGuiKey_V)) do_paste();
      else if (ImGui::IsKeyPressed(ImGuiKey_S)) save_to("spreadsheet.txt");
      else if (ImGui::IsKeyPressed(ImGuiKey_O)) load_from("spreadsheet.txt");
      else if (ImGui::IsKeyPressed(ImGuiKey_N)) clear_sheet();
    }
  }

  Spreadsheet::Sheet sheet_;
  std::vector<EditBuf> edits_;
  std::deque<Spreadsheet::Sheet> undo_;
  std::deque<Spreadsheet::Sheet> redo_;
  std::string clipboard_;
  int selected_ = -1;
  int editing_ = -1;
  bool just_started_editing_ = false;
  bool show_about_ = false;
};

void glfw_error(int err, const char* desc) {
  std::fprintf(stderr, "GLFW %d: %s\n", err, desc);
}

}  // namespace

int main() {
  glfwSetErrorCallback(glfw_error);
  if (!glfwInit()) return 1;

  glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 3);
  glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 3);
  glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);

  GLFWwindow* win = glfwCreateWindow(1280, 800, "Crane Spreadsheet", nullptr, nullptr);
  if (!win) { glfwTerminate(); return 1; }
  glfwMakeContextCurrent(win);
  glfwSwapInterval(1);

  IMGUI_CHECKVERSION();
  ImGui::CreateContext();
  ImGui::StyleColorsDark();
  ImGui_ImplGlfw_InitForOpenGL(win, true);
  ImGui_ImplOpenGL3_Init("#version 330 core");

  App app;
  while (!glfwWindowShouldClose(win)) {
    glfwPollEvents();
    ImGui_ImplOpenGL3_NewFrame();
    ImGui_ImplGlfw_NewFrame();
    ImGui::NewFrame();

    ImGuiViewport* vp = ImGui::GetMainViewport();
    ImGui::SetNextWindowPos(vp->WorkPos);
    ImGui::SetNextWindowSize(vp->WorkSize);
    app.render();

    ImGui::Render();
    int w, h;
    glfwGetFramebufferSize(win, &w, &h);
    glViewport(0, 0, w, h);
    glClearColor(0.10f, 0.10f, 0.12f, 1.0f);
    glClear(GL_COLOR_BUFFER_BIT);
    ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());
    glfwSwapBuffers(win);
  }

  ImGui_ImplOpenGL3_Shutdown();
  ImGui_ImplGlfw_Shutdown();
  ImGui::DestroyContext();
  glfwDestroyWindow(win);
  glfwTerminate();
  return 0;
}
