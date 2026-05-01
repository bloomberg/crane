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
#include <string>
#include <vector>

namespace {

constexpr int NUM_COLS = 26;
constexpr int NUM_ROWS = 100;

// Per-cell editing state.  Holds the source string the user is typing,
// independent of the kernel's evaluated value.  When the user commits
// (Enter or focus lost), we parse and write back into the kernel.
struct EditBuf {
  std::array<char, 128> buf{};
};

class App {
 public:
  App() : sheet_(Spreadsheet::new_sheet) {
    edits_.resize(NUM_COLS * NUM_ROWS);
  }

  void render() {
    if (ImGui::Begin("Crane Spreadsheet", nullptr, ImGuiWindowFlags_MenuBar)) {
      menu_bar();

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
          char label[2] = {static_cast<char>('A' + c), '\0'};
          ImGui::TableSetupColumn(label, ImGuiTableColumnFlags_WidthFixed, 80.0f);
        }
        ImGui::TableHeadersRow();

        for (int r = 0; r < NUM_ROWS; ++r) {
          ImGui::TableNextRow();
          ImGui::TableSetColumnIndex(0);
          ImGui::Text("%d", r + 1);
          for (int c = 0; c < NUM_COLS; ++c) {
            ImGui::TableSetColumnIndex(c + 1);
            cell_widget(c, r);
          }
        }
        ImGui::EndTable();
      }
    }
    ImGui::End();
  }

 private:
  void menu_bar() {
    if (ImGui::BeginMenuBar()) {
      if (ImGui::BeginMenu("File")) {
        if (ImGui::MenuItem("New")) {
          sheet_ = Spreadsheet::new_sheet;
          for (auto& e : edits_) e.buf[0] = '\0';
        }
        ImGui::EndMenu();
      }
      if (ImGui::BeginMenu("Help")) {
        ImGui::TextUnformatted(
            "Type a number to set a literal.\n"
            "Type =A1+B2 etc. to set a formula.\n"
            "Operators: + - * / and parentheses.\n"
            "Empty input clears the cell.");
        ImGui::EndMenu();
      }
      ImGui::EndMenuBar();
    }
  }

  int idx(int c, int r) const { return r * NUM_COLS + c; }

  void cell_widget(int c, int r) {
    EditBuf& eb = edits_[idx(c, r)];

    ImGui::PushID(idx(c, r));
    ImGui::SetNextItemWidth(-FLT_MIN);

    // The label shown when the cell is not focused: the evaluated value
    // (or "#ERR" if the formula failed).  When focused, ImGui shows the
    // raw source the user is editing.
    if (ImGui::InputText("##cell", eb.buf.data(), eb.buf.size(),
                         ImGuiInputTextFlags_EnterReturnsTrue |
                         ImGuiInputTextFlags_AutoSelectAll)) {
      commit(c, r);
    }
    bool focused = ImGui::IsItemActive();
    if (!focused) {
      // Overlay the evaluated value on top of the input.  We do this by
      // drawing text aligned to the same rect.  Simple approach: when the
      // user is not editing, show the evaluated value via tooltip /
      // overlay.  For minimum noise we show it directly when buf is empty
      // for non-formula cells, otherwise show a separate display string.
      auto display = display_for(c, r, eb);
      if (display && !focused) {
        ImVec2 rect_min = ImGui::GetItemRectMin();
        ImVec2 rect_max = ImGui::GetItemRectMax();
        ImDrawList* dl = ImGui::GetWindowDrawList();
        // Overpaint with the cell's background colour, then write the
        // evaluated value.  We use the BG and Text cols from the style.
        ImU32 bg = ImGui::GetColorU32(ImGuiCol_FrameBg);
        ImU32 fg = ImGui::GetColorU32(ImGuiCol_Text);
        dl->AddRectFilled(rect_min, rect_max, bg);
        ImVec2 pad = ImGui::GetStyle().FramePadding;
        dl->AddText({rect_min.x + pad.x, rect_min.y + pad.y}, fg,
                    display->c_str());
      }
    }
    ImGui::PopID();
  }

  // Build the string to display when the cell is not being edited.
  std::optional<std::string> display_for(int c, int r, const EditBuf& eb) {
    Spreadsheet::CellRef ref{static_cast<int64_t>(c), static_cast<int64_t>(r)};
    auto cell = Spreadsheet::get_cell(sheet_, ref);
    if (std::holds_alternative<Spreadsheet::Cell::CEmpty>(cell.v())) {
      return std::nullopt;  // show the empty input
    }
    auto val = Spreadsheet::eval_cell(Spreadsheet::DEFAULT_FUEL, sheet_, ref);
    if (!val) return std::string("#ERR");
    return std::to_string(*val);
  }

  void commit(int c, int r) {
    EditBuf& eb = edits_[idx(c, r)];
    Spreadsheet::CellRef ref{static_cast<int64_t>(c), static_cast<int64_t>(r)};
    std::string_view src(eb.buf.data());
    while (!src.empty() && std::isspace(static_cast<unsigned char>(src.front())))
      src.remove_prefix(1);

    if (src.empty()) {
      sheet_ = Spreadsheet::set_cell(sheet_, ref, Spreadsheet::Cell::cempty());
      return;
    }
    if (src.front() == '=') {
      auto e = formula::parse(src.substr(1));
      if (!e) {
        // Leave the buffer alone but mark the cell as a literal "0" so
        // the user can see something happened?  For now: keep the old
        // value, surface the parse failure via tooltip.
        // TODO(spreadsheet): persist parse-failure state per cell.
        return;
      }
      sheet_ = Spreadsheet::set_cell(sheet_, ref,
          Spreadsheet::Cell::cform(std::move(*e)));
      return;
    }
    // Plain integer literal.
    int64_t v = 0;
    bool neg = false;
    size_t i = 0;
    if (src[i] == '-') { neg = true; ++i; }
    bool any = false;
    while (i < src.size() && std::isdigit(static_cast<unsigned char>(src[i]))) {
      v = v * 10 + (src[i] - '0');
      ++i;
      any = true;
    }
    if (any && i == src.size()) {
      sheet_ = Spreadsheet::set_cell(sheet_, ref,
          Spreadsheet::Cell::clit(neg ? -v : v));
    }
  }

  Spreadsheet::Sheet sheet_;
  std::vector<EditBuf> edits_;
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

    // Cover the whole client area with the spreadsheet window.
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
