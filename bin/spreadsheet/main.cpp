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

const int NUM_COLS = static_cast<int>(Spreadsheet::NUM_COLS);
const int NUM_ROWS = static_cast<int>(Spreadsheet::NUM_ROWS);

// Per-cell editing state.  Holds the source string the user is typing
// (independent of the kernel's evaluated value), plus a flag that records
// whether the last commit failed to parse.  Setting [parse_error] makes
// the cell render "#PARSE" in place of an evaluated value.
struct EditBuf {
  std::array<char, 128> buf{};
  bool parse_error = false;
};

class App {
 public:
  App() : sheet_(Spreadsheet::new_sheet) {
    edits_.resize(static_cast<size_t>(NUM_COLS) * NUM_ROWS);
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
          std::string label = formula::label_of(c, 0);
          // label_of returns "<col><row+1>", strip the row part for headers.
          while (!label.empty() &&
                 std::isdigit(static_cast<unsigned char>(label.back()))) {
            label.pop_back();
          }
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
  }

 private:
  void menu_bar() {
    if (ImGui::BeginMenuBar()) {
      if (ImGui::BeginMenu("File")) {
        if (ImGui::MenuItem("New")) {
          sheet_ = Spreadsheet::new_sheet;
          for (auto& e : edits_) {
            e.buf[0] = '\0';
            e.parse_error = false;
          }
        }
        ImGui::EndMenu();
      }
      if (ImGui::BeginMenu("Help")) {
        ImGui::TextUnformatted(
            "Type a number to set a literal.\n"
            "Type =A1+B2 etc. to set a formula.\n"
            "Operators: + - * / and parentheses.\n"
            "Empty input clears the cell.\n"
            "#PARSE - the formula didn't parse.\n"
            "#ERR   - cycle, division by zero, or out of fuel.");
        ImGui::EndMenu();
      }
      ImGui::EndMenuBar();
    }
  }

  size_t idx(int c, int r) const {
    return static_cast<size_t>(r) * NUM_COLS + c;
  }

  void cell_widget(int c, int r) {
    EditBuf& eb = edits_[idx(c, r)];

    ImGui::PushID(static_cast<int>(idx(c, r)));
    ImGui::SetNextItemWidth(-FLT_MIN);

    if (ImGui::InputText("##cell", eb.buf.data(), eb.buf.size(),
                         ImGuiInputTextFlags_EnterReturnsTrue |
                         ImGuiInputTextFlags_AutoSelectAll)) {
      commit(c, r);
    }
    bool focused = ImGui::IsItemActive();

    if (!focused) {
      auto display = display_for(c, r, eb);
      if (display) {
        ImVec2 rect_min = ImGui::GetItemRectMin();
        ImVec2 rect_max = ImGui::GetItemRectMax();
        ImDrawList* dl = ImGui::GetWindowDrawList();
        ImU32 bg = ImGui::GetColorU32(ImGuiCol_FrameBg);
        ImU32 fg = ImGui::GetColorU32(ImGuiCol_Text);
        if (eb.parse_error || (display->size() >= 4 &&
                                display->compare(0, 4, "#ERR") == 0)) {
          fg = IM_COL32(220, 80, 80, 255);
        }
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

  void commit(int c, int r) {
    EditBuf& eb = edits_[idx(c, r)];
    Spreadsheet::CellRef ref{static_cast<int64_t>(c), static_cast<int64_t>(r)};
    std::string_view src(eb.buf.data());
    while (!src.empty() && std::isspace(static_cast<unsigned char>(src.front())))
      src.remove_prefix(1);

    if (src.empty()) {
      sheet_ = Spreadsheet::set_cell(sheet_, ref, Spreadsheet::Cell::cempty());
      eb.parse_error = false;
      return;
    }
    if (src.front() == '=') {
      auto e = formula::parse(src.substr(1));
      if (!e) {
        eb.parse_error = true;
        return;
      }
      sheet_ = Spreadsheet::set_cell(sheet_, ref,
          Spreadsheet::Cell::cform(std::move(*e)));
      eb.parse_error = false;
      return;
    }
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
      eb.parse_error = false;
    } else {
      eb.parse_error = true;
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
