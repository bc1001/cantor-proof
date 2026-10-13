# 0-1 受限数位无限小数乘积猜想的形式化机器证明
### Formal Proof of the Restricted-Digit Decimal Product Conjecture in Lean 4

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.35.0--rc4-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-verified-green.svg)](https://github.com/leanprover-community/mathlib4)
[![Build & Comparator](https://img.shields.io/badge/Comparator-0_drift-success.svg)](#-验证与可信度)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

本仓库包含了对以下数学猜想的**完整形式化机器证明（0 sorry, 0 自定义公理）**，所有推导均基于 **Lean 4 / Mathlib** 并在 CI 自动化流水线中通过了形式化对比器（Comparator）的双向抽象语法树（AST）无偏差核验。

---

## 📌 命题陈述 (Problem Statement)

> **猜想 1**：  
> 对于任意非零实数 $y \in \mathbb{R} \setminus \{0\}$，均可以表示为有限个属于集合 $S$ 的数之乘积。  
> 其中数集 $S$ 定义为：绝对值满足 $0 < |x| \le 1.2$，且其在十进制表示下，整数部分与小数部分每一位数位均只能取 $0$ 或 $1$，且小数部分含有无穷多个 $1$（即严格非终止的无限小数）。

---

## 🌟 核心突破与数学架构 (Key Breakthroughs)

该命题表面看似初等，实则深陷非线性仿射康托集的微观共振与空隙（Cantor Gaps）泥潭。本证明完全摒弃了未证的世界级猜想（如泛型 Palis 猜想），完全依靠第一性原理，设计了一套纯构造性的离散动力系统：

1. **20 因子大冗余度压制**：  
   摒弃了紧绷的 4 因子或 10 因子，果断选用 $d=20$ 个因子。将单步离散跃迁步长控制在 $\le 1.03 \cdot 10^{-(n+3)}$ 之内，而剩余尾部的支配跨度高达 $\frac{19}{9} \cdot 10^{-(n+3)} \approx 2.11 \cdot 10^{-(n+3)}$。数量级的代数富余量直接在物理上淹没了非线性曲率形变。
2. **局部冰冻窗口 $[1.002, 1.003]$**：  
   将目标限制在极度贴近 1 的窗口，使得因子增长受限于 $1 \le f_j \le 1 + 1/900$，导数膨胀被严格锁定在 $1.03$ 以内。
3. **循环游标（Cyclic Cursor）与严格单调贪心**：  
   * **负载均衡**：通过模 $20$ 游标循环轮换分配数位，防止前置因子超标；
   * **破除停机陷阱**：保持严格小于 $P_n < x$，残差永远大于 0，迫使游标无限发散，**严格证明了每一个因子都分到了无穷多个 1（严格无限小数）**。
4. **宏观分析学延拓**：  
   * 徒手证明伯努利不等式与相邻区间重叠；
   * 构造实数方根 $t = y^{1/n}$ 将局部闭区间延拓至无穷半射线 $[M, \infty)$；
   * 严格证明等比级数 $\sum 10^{-(n+1)} = 1/9$，利用 $\pm 1/9 \in S$ 完成全正实轴与负数镜像翻转。

---

## 🛡 验证与可信度 (Integrity & Verification)

本证明在形式化工程规范上达到了最高级别的纯净性：

* **零自定义公理 (Zero Custom Axioms)**：  
  运行 `#print axioms StrictFormalConjecture1.Conjecture1`，全证明**仅依赖 Lean 4 核心的三大标准逻辑公理**：
  ```text
  [propext, Classical.choice, Quot.sound]
  ```
* **零占位符 (Zero Sorry)**：  
  全量代码无任何 `sorry` 或未完成分支。
* **双向 AST 比对 (0 Specification Drift)**：  
  仓库内置独立的自动化对比器（Comparator）。CI 流水线会在独立的内存沙盒中动态加载目标规范与解题模块，严格验证定理签名一致：
  ```text
  === Comparator AST Verification for StrictFormalConjecture1.Conjecture1 ===
  ✔ Comparator verified: Target theorem types are identical (0 drift)!
  ```

---

## 📂 仓库结构 (Repository Structure)

```text
.
├── .github/workflows/
│   └── build.yml               # 自动化构建、缓存拉取与 Comparator 校验流水线
├── StrictFormalConjecture1.lean # 包含全部推导的 1500 行完全独立机器证明文件
├── Conjecture1_Comparator.lean  # 目标命题的不可变抽象规范（试卷）
├── lakefile.lean               # 注册试卷与答卷双模块的 Lake 配置文件
├── lean-toolchain              # 锁死编译器版本 (leanprover/lean4:v4.35.0-rc4)
└── lake-manifest.json          # 锁死 Mathlib 依赖精确 Git Hash 的契约表
```

---

## 🚀 本地复现与构建 (How to Reproduce)

任何人均可在本地一键复现并核验整个证明：

### 1. 克隆仓库
```bash
git clone https://github.com/bc1001/cantor-proof.git
cd cantor-proof
```

### 2. 获取预编译缓存并构建
```bash
# 自动拉取与 v4.35.0-rc4 完全匹配的 Mathlib 二进制缓存
lake exe cache get

# 构建生成 .olean 内核目标文件
lake build StrictFormalConjecture1 Conjecture1_Comparator
```

### 3. 运行本地 Comparator 校验
```bash
lake env lean --run - << 'EOF'
import Lean
open Lean

def main : IO Unit := do
  let envChallenge ← importModules #[{ module := `Conjecture1_Comparator }] {}
  let envSolution ← importModules #[{ module := `StrictFormalConjecture1 }] {}
  let targetName := `StrictFormalConjecture1.Conjecture1
  match envChallenge.find? targetName, envSolution.find? targetName with
  | some c1, some c2 =>
    if c1.type == c2.type then
      IO.println "✔ Local Comparator verified: Target theorem types are identical!"
    else
      throw <| IO.userError "Type mismatch detected!"
  | _, _ => throw <| IO.userError "Declaration not found!"
EOF
```

---

## 💡 致谢与研发范式 (Credits & Methodology)

本项目的成功证明是**人类架构师、前沿生成式大语言模型（LLM）与形式化编译器（Lean 4）深度协同**的产物：
* **人类架构师**：负责提出规范锁死边界、识别伪证与假公理陷阱、拆解子任务并规划 20 因子局部化与游标调度路线；
* **AI 推理集群**：负责高通量的符号推演、战术搜索与 $\varepsilon$-$\delta$ 细粒度代数代码生成；
* **Lean 4 / Mathlib**：充当冷酷、客观的最高裁判，提供绝对无瑕疵的真理基准。

---

## 📄 开源许可证 (License)

本项目采用 [MIT License](LICENSE) 开源协议。
