# 測試說明：CTUS 與 Fixed-N 採樣演算法

本文件旨在說明如何編譯、執行並視覺化 `CTUS` 和 `Fixed-N` 這兩種自訂採樣演算法的成功率與性能測試。

## 1. 環境準備

在開始之前，請確保您的系統已安裝以下工具與函式庫：

- **建構工具**: `cmake`, C 編譯器 (如 `gcc` 或 `clang`)
- **Python 3**: 用於執行視覺化腳本。
- **Python 函式庫**: `pandas`, `matplotlib`, `seaborn`。

## 2. 程式碼結構

為了進行可參數化的測試，我們進行了以下修改，這些修改被包裹在 `OQS_ENABLE_TESTING` 宏定義中，以確保它們不會影響正式的程式庫編譯。

1.  **新增可測試函式**：在 `src/kem/hqc/pqclean_hqc-128_clean/vector.c` 中新增了兩個函式：
    - `PQCLEAN_HQC128_CLEAN_vect_generate_random_support_ctus_testable()`
    - `PQCLEAN_HQC128_CLEAN_vect_generate_random_support_fixed_n_testable()`
    這些函式允許將 `factor` 作為參數傳入。

2.  **建立測試主程式**：建立了一個新的測試檔案 `tests/test_sampling_success.c`，它包含了執行批量測試、計時和統計成功/失敗次數的邏輯。

3.  **修改建構系統**：在 `tests/CMakeLists.txt` 中，新增了專門的規則來編譯上述測試程式，並將所有相依的 `.c` 檔案（如 `vector.c`, `shake_prng.c` 等）都一起編譯進來，以解決連結器依賴問題。

## 3. 如何執行測試與分析

請依照以下步驟從專案根目錄執行。

### 步驟 3.1: 編譯測試程式

首先，我們需要設定 CMake 並指定建構 `test_sampling_success` 這個目標。

```bash
# 步驟 1: 設定建構目錄 (如果已設定過可跳過)
cmake -S . -B build

# 步驟 2: 編譯指定的測試程式
cmake --build build --target test_sampling_success
```

### 步驟 3.2: 執行測試並產生數據

執行剛剛編譯好的程式。您可以提供一個檔名作為命令列參數，測試結果將會以 CSV 格式儲存到該檔案中。推薦使用 `.csv` 副檔名。

```bash
# 執行測試，並將結果儲存到 sampling_results_final.csv
./build/tests/test_sampling_success sampling_results_final.csv
```

此過程會花費數分鐘，具體時間取決於您的機器性能以及 `test_sampling_success.c` 中設定的迭代次數。

### 步驟 3.3: 視覺化測試結果

我們使用 `visualize_results.py` 腳本來分析產生的 CSV 檔案並繪製圖表。

```bash
# 步驟 1: 建立並啟用 Python 虛擬環境 (若 .venv 已存在則不需重複建立)
python3 -m venv .venv

# 步驟 2: 啟用虛擬環境並安裝必要的函式庫
source .venv/bin/activate
python3 -m pip install pandas matplotlib seaborn

# 步驟 3: 執行繪圖腳本
python3 visualize_results.py
```

腳本執行完畢後，所有生成的圖表（`.png` 檔案）將會被保存在 `test_visualizations/` 資料夾中。

## 4. 如何修改測試參數

如果您未來需要測試不同的 `weight` 或 `factor` 組合，可以直接修改 `tests/test_sampling_success.c` 中的 `main` 函式：

- **`weights_to_test[]`**: 修改此陣列以測試不同的 `weight` 值。
- **`iterations`**: 修改此變數以調整每個參數組合的測試次數。
- **`ctus_factors[]`** 和 **`n_factors[]`**: 修改這些陣列以調整您想測試的 `factor` 範圍和密度。

修改完畢後，只需重複 **步驟 3.1** 重新編譯，然後執行後續步驟即可。
