# Cleanup and Refactoring Plan

## 1. Core Logic & Architecture
* **clpBNR Migration**: Convert shape calculation from `clpfd` to `clpBNR` to allow seamless mixing of shape and range constraints.
* **Modular Runtime**: Clean up multifile predicates across the backend interfaces (`runtime_prolog.pl`, `runtime_c.pl`, `array.pl`) to ensure a clean, modular runtime.

## 2. Project Structure & Packaging
* **SWI-Prolog Pack**: Reorganize the repository files to follow a proper SWI-Prolog pack directory structure.
* **Build System**: Add pack metadata (`pack.pl`) and C extension build files (`CMakeLists.txt` or `Makefile`) to automate the compilation of `buffer.c` and other C artifacts.

## 3. Code Reorganization & Quality
* **Refactor `array.pl`**: Reorganize the file's internal layout so it is easier to navigate.
* **Dead Code Removal**: Clean up dead or commented-out code (e.g., old multifile declarations in `array.pl`, commented DType rules in `runtime_prolog.pl`).
* **Handle Stubs**: Address or properly track `not_implemented` stubs (e.g., `solve` in `runtime_c.pl`).

## 4. Testing
* **Extract Tests**: Split the `:- begin_tests(...)` blocks out of the implementation files and move them into a dedicated `tests/` directory.
* **Improve Coverage**: Expand the test suites to achieve better overall code coverage.

## 5. Documentation
* **PlDoc Comments**: Standardize and write PlDoc documentation strings (`%!`) for important predicates across the codebase.
* **NumPy Tutorial**: Write a guide/tutorial tailored for users who are already familiar with NumPy.
