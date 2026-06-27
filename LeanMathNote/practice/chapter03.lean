--#--
/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda
-/
--#--
/-
# Chapter 03: 位相

Mathlib における基本的な位相を扱います．

参考:

* Mathematics in Lean, 11. Topology: <https://leanprover-community.github.io/mathematics_in_lean/C11_Topology.html>
* Maths in Lean: Topological, uniform and metric spaces: <https://leanprover-community.github.io/theories/topology.html>

フィルター，距離空間，位相空間，連続性，コンパクト性などが説明されています．

Lean での位相はフィルターに基づいて形式化されています．
フィルターは，数列の極限，関数の極限，無限遠での振る舞い，近傍などを同じ言葉で扱うための道具です．
-/

import Mathlib
set_option linter.missingDocs false --#

namespace PracticeChapter03

open Set Filter
open scoped Topology

/-
---
## 位相空間

位相空間構造は `TopologicalSpace X` です．
開集合は `IsOpen U`，閉集合は `IsClosed C` と書きます．
`interior`，`closure`，`frontier` なども `Set X` に対する操作です．

Mathlib では，位相空間構造の中に開集合を表す述語が入っています．
`IsOpen` はその述語を取り出したものです．
一方，`IsClosed C` は独立した原始概念ではなく，補集合 `Cᶜ` が開集合であることとして定義されています．

```lean title="Mathlib/Topology/Defs/Basic.lean"
class TopologicalSpace (X : Type u) where
  protected IsOpen : Set X → Prop
  protected isOpen_univ : IsOpen univ
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

def IsOpen : Set X → Prop := TopologicalSpace.IsOpen

class IsClosed (s : Set X) : Prop where
  isOpen_compl : IsOpen sᶜ
```

したがって，閉集合に関する主張は，補集合を取ると開集合に関する主張として読めます．
-/

#check TopologicalSpace
#check IsOpen
#check IsClosed
#check interior
#check closure
#check frontier

section TopologicalSpaces

variable {X : Type*} [TopologicalSpace X]
variable {U V C D Y Z : Set X}

example (hU : IsOpen U) (hV : IsOpen V) : IsOpen (U ∩ V) := by
  exact hU.inter hV

example (hC : IsClosed C) (hD : IsClosed D) : IsClosed (C ∪ D) := by
  exact hC.union hD

example : IsOpen Cᶜ ↔ IsClosed C := by
  exact isOpen_compl_iff

example : interior Y = Y ↔ IsOpen Y := by
  exact interior_eq_iff_isOpen

example (hYZ : Y ⊆ Z) : interior Y ⊆ interior Z := by
  exact interior_mono hYZ

example : closure Y = Y ↔ IsClosed Y := by
  exact closure_eq_iff_isClosed

example (hYZ : Y ⊆ Z) : closure Y ⊆ closure Z := by
  exact closure_mono hYZ

end TopologicalSpaces

/-
集合の等式や包含と同じように，位相的な操作も `Set` の補題と組み合わせて使います．
たとえば，`closure_mono` は集合の包含から閉包の包含を得る補題です．
-/

/-
### 演習問題

1. `closure_mono` を使って，`s ⊆ t` なら `closure s ⊆ closure t` を示してください．

    ```lean4
    example {X : Type*} [TopologicalSpace X] {s t : Set X} (hst : s ⊆ t) :
        closure s ⊆ closure t := by
      -- ヒント: `exact closure_mono hst`
      -- 解答例: exact closure_mono hst
      sorry
    ```

2. `interior s ⊆ s` と `s ⊆ closure s` をそれぞれ確認してください．

    ```lean4
    -- 解答例: `interior_subset` が `interior s ⊆ s`，
    -- `subset_closure` が `s ⊆ closure s` を述べます．
    #check interior_subset
    #check subset_closure
    ```
-/

--#--
example {X : Type*} [TopologicalSpace X] {s t : Set X} (hst : s ⊆ t) :
    closure s ⊆ closure t := by
  -- ヒント: `exact closure_mono hst`
  -- 解答例: exact closure_mono hst
  sorry

-- 解答例: `interior_subset` が `interior s ⊆ s`，
-- `subset_closure` が `s ⊆ closure s` を述べます．
#check interior_subset
#check subset_closure
--#--

/-
---
## フィルター

`Filter α` は，`α` の部分集合のうち，どれをフィルターに含めるかを指定する構造です．
数学的には，集合 $X$ 上のフィルター $\mathcal F$ は，部分集合族
$\mathcal F \subseteq \mathcal P(X)$ であって，次を満たすものです．

$$
X \in \mathcal F,
\qquad
A, B \in \mathcal F \Longrightarrow A \cap B \in \mathcal F,
\qquad
A \in \mathcal F,\ A \subseteq B \subseteq X \Longrightarrow B \in \mathcal F.
$$

通常の数学ではさらに $\emptyset \notin \mathcal F$ も仮定します．
Lean の `Filter X` ではこの条件は定義には入っていませんが，
この章で扱う `atTop` や `𝓝 x` を読むうえでは，まず意識しなくてかまいません．

この章では，フィルターの一般論よりも，次の 3 つの読み方が重要です．
型 `α` 上のフィルター `l : Filter α` を考えます．

* `s ∈ l`: `s : Set α` は `α` の部分集合であり，
  `s` がフィルター `l` に含まれる，という意味です．
* `∀ᶠ x in l, p x`: `x : α` は集合ではなく，`α` の点を表す束縛変数です．
  `p : α → Prop` に対して，`p x` が成り立つような点 `x` 全体の集合が，
  フィルター `l` に含まれる，という意味です．
  定義上は `{x : α | p x} ∈ l` という主張です．
* `Tendsto f l m`: `x : α` が `l` に沿って動くとき，`f x` が `m` に沿って動く．

数式で書くと，`∀ᶠ x in l, p x` は

$$
\{x \in X \mid p(x)\} \in \mathcal F
$$

という条件です．
また，写像 $f : X \to Y$ とフィルター $\mathcal F$，$\mathcal G$ について
`Tendsto f l m` は，次の条件に対応します．

$$
\forall B \in \mathcal G,\quad f^{-1}(B) \in \mathcal F.
$$

この章で主に使うフィルターは，`atTop` と `𝓝 x` です．

`atTop` は，順序集合の「上の方へ行く」ことを表すフィルターです．
自然数上では「十分大きい `n`」を意味します．
自然数上の部分集合 $S \subseteq \mathbb N$ については，

$$
S \in \mathrm{atTop}
\quad\Longleftrightarrow\quad
\exists N,\ \forall n \ge N,\ n \in S
$$

と読めます．
この講義では，次の補題を `atTop` の定義のように読めば十分です．

```lean title="Mathlib/Order/Filter/AtTopBot/Basic.lean"
lemma mem_atTop_sets :
    s ∈ (atTop : Filter α) ↔ ∃ a : α, ∀ b ≥ a, b ∈ s

lemma eventually_atTop :
    (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b ≥ a, p b
```

特に自然数列の命題 `P : ℕ → Prop` について，`∀ᶠ m in atTop, P m` は
「ある `n` が存在して，`n ≤ m` なる任意の `m` について `P m`」という意味です．
数式で書けば，

$$
\forall^{\mathrm{eventually}} m,\ P(m)
\quad\Longleftrightarrow\quad
\exists N,\ \forall m \ge N,\ P(m)
$$

です．
つまり，有限個の初期項を除けば `P m` が常に成り立つ，ということです．

一方，`𝓝 x` は点 `x` の近傍フィルターです．
`s ∈ 𝓝 x` は，`s` が `x` の近傍であることを意味します．
位相空間 $X$ の点 $x$ と部分集合 $S \subseteq X$ については，

$$
S \in \mathcal N(x)
\quad\Longleftrightarrow\quad
\exists U,\ x \in U,\ U \text{ is open},\ U \subseteq S.
$$

実際には，次の補題で読むのが便利です．

```lean title="Mathlib/Topology/Neighborhoods.lean"
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t
```

つまり，`s` が `x` の近傍であるとは，`s` の中に `x` を含む開集合 `t` があることです．

`Tendsto f l m` は，「`x` がフィルター `l` に沿って動くとき，`f x` がフィルター `m` に沿って動く」という意味です．
数列の極限も，関数の一点での極限も，無限遠での極限も，この形で表されます．
内部的には `map f l ≤ m` という定義ですが，まずは
「`m` に含まれる任意の集合の逆像は，`l` に含まれる」と読むのがよいです．
-/

#check Filter
#check Tendsto
#check atTop
#check 𝓝
#check Filter.Eventually
#check mem_atTop_sets
#check eventually_atTop
#check mem_nhds_iff

section Filters

example {α : Type*} {l : Filter α} {p : α → Prop} :
    (∀ᶠ x in l, p x) = ({x | p x} ∈ l) := by
  rfl

example : (∀ᶠ n in (atTop : Filter Nat), 3 ≤ n) := by
  exact eventually_ge_atTop 3

example {P : ℕ → Prop} :
    (∀ᶠ m in (atTop : Filter ℕ), P m) ↔ ∃ n, ∀ m, n ≤ m → P m := by
  exact eventually_atTop

example {s : Set ℕ} :
    s ∈ (atTop : Filter ℕ) ↔ ∃ n, ∀ m, n ≤ m → m ∈ s := by
  exact mem_atTop_sets

example {X : Type*} [TopologicalSpace X] {x : X} {s : Set X} :
    s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t := by
  exact mem_nhds_iff

example {α β : Type*} {f : α → β} {l : Filter α} {m : Filter β} :
    Tendsto f l m = (map f l ≤ m) := by
  rfl

end Filters

/-
### 近傍フィルターで収束と連続を読む

この節で使う対応は次の 2 つです．

$$
\mathcal N(x) = \text{the neighborhood filter of } x,
$$

すなわち

$$
A \in \mathcal N(x)
\quad\Longleftrightarrow\quad
\exists U,\ x \in U,\ U \text{ is open},\ U \subseteq A.
$$

また，写像 $f : X \to Y$ について

$$
\operatorname{Tendsto}(f,\mathcal F,\mathcal G)
\quad\Longleftrightarrow\quad
\forall B \in \mathcal G,\ f^{-1}(B) \in \mathcal F.
$$

点列 `u : ℕ → X` が `x` に収束することは，次のように書きます．

```lean4
Tendsto u atTop (𝓝 x)
```

これは数式では，

$$
\operatorname{Tendsto}(u,\mathrm{atTop},\mathcal N(x))
\quad\Longleftrightarrow\quad
\forall A \in \mathcal N(x),\ \{n \in \mathbb N \mid u_n \in A\} \in \mathrm{atTop}
$$

です．
さらに，$\mathrm{atTop}$ を

$$
S \in \mathrm{atTop}
\quad\Longleftrightarrow\quad
\exists N,\ \forall n \ge N,\ n \in S
$$

と読むと，これは通常の点列収束

$$
u_n \to x
\quad\Longleftrightarrow\quad
\forall U,
\bigl(U \text{ is open} \land x \in U\bigr)
\Longrightarrow
\exists N,\ \forall n \ge N,\ u_n \in U
$$

と同じです．
`tendsto_nhds` は，この条件を開集合で読むための補題です．

```lean title="Mathlib/Topology/Neighborhoods.lean"
theorem tendsto_nhds {a : X} {f : α → X} {l : Filter α} :
    Tendsto f l (𝓝 a) ↔
      ∀ s, IsOpen s → a ∈ s → f ⁻¹' s ∈ l
```

対応する証明は，次の式変形として読めます．

まず $U$ が $x$ を含む開集合なら

$$
x \in U,\ U \text{ is open}
\quad\Longrightarrow\quad
U \in \mathcal N(x).
$$

したがって

$$
\operatorname{Tendsto}(u,\mathrm{atTop},\mathcal N(x))
\quad\Longrightarrow\quad
u^{-1}(U) \in \mathrm{atTop}
\quad\Longleftrightarrow\quad
\exists N,\ \forall n \ge N,\ u_n \in U.
$$

逆向きでは，任意の $A \in \mathcal N(x)$ に対して

$$
A \in \mathcal N(x)
\quad\Longrightarrow\quad
\exists U,\ x \in U,\ U \text{ is open},\ U \subseteq A.
$$

仮定より

$$
\exists N,\ \forall n \ge N,\ u_n \in U.
$$

$U \subseteq A$ なので

$$
\exists N,\ \forall n \ge N,\ u_n \in A,
$$

すなわち

$$
u^{-1}(A) \in \mathrm{atTop}.
$$

一点 `x` での連続性も，同じ `Tendsto` で定義されます．

```lean title="Mathlib/Topology/Defs/Filter.lean"
def ContinuousAt (f : X → Y) (x : X) :=
  Tendsto f (𝓝 x) (𝓝 (f x))
```

数式では，

$$
f \text{ is continuous at } x
\quad\Longleftrightarrow\quad
\forall V \in \mathcal N(f(x)),\ f^{-1}(V) \in \mathcal N(x)
$$

です．
開集合で書けば，

$$
f \text{ is continuous at } x
\quad\Longleftrightarrow\quad
\forall V,
\bigl(V \text{ is open} \land f(x) \in V\bigr)
\Longrightarrow
\exists U,\ x \in U,\ U \text{ is open},\ U \subseteq f^{-1}(V).
$$

大域的な連続性は，次の補題により「開集合の逆像が開集合」と同値になります．
すなわち，

$$
f \text{ is continuous}
\quad\Longleftrightarrow\quad
\forall V \subseteq Y,
V \text{ is open} \Longrightarrow f^{-1}(V) \text{ is open}.
$$

```lean title="Mathlib/Topology/Continuous.lean"
theorem continuous_def :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

theorem continuous_iff_continuousAt :
    Continuous f ↔ ∀ x, ContinuousAt f x
```

この同値性の証明も，近傍の式で追えます．
各点で

$$
\forall x,\ \forall A \in \mathcal N(f(x)),\ f^{-1}(A) \in \mathcal N(x)
$$

が成り立つとします．
$V \subseteq Y$ が開集合なら，

$$
x \in f^{-1}(V)
\quad\Longrightarrow\quad
f(x) \in V
\quad\Longrightarrow\quad
V \in \mathcal N(f(x)).
$$

よって

$$
f^{-1}(V) \in \mathcal N(x)
\qquad (x \in f^{-1}(V)).
$$

任意の点 $x \in f^{-1}(V)$ で $f^{-1}(V)$ が $x$ の近傍なので，

$$
f^{-1}(V) \text{ is open}.
$$

逆に，

$$
\forall V \subseteq Y,
V \text{ is open} \Longrightarrow f^{-1}(V) \text{ is open}
$$

を仮定します．
$A \in \mathcal N(f(x))$ なら

$$
\exists V,\ f(x) \in V,\ V \text{ is open},\ V \subseteq A.
$$

このとき

$$
x \in f^{-1}(V),\qquad f^{-1}(V) \text{ is open},\qquad
f^{-1}(V) \subseteq f^{-1}(A).
$$

したがって

$$
f^{-1}(A) \in \mathcal N(x).
$$

これは

$$
\operatorname{Tendsto}(f,\mathcal N(x),\mathcal N(f(x)))
$$

です．
-/

#check tendsto_nhds
#check continuous_def
#check continuous_iff_continuousAt

section NeighborhoodFilters

example {X : Type*} [TopologicalSpace X] (x : X) : Filter X :=
  𝓝 x

example {X : Type*} [TopologicalSpace X] {u : ℕ → X} {U : Set X} :
    (u ⁻¹' U ∈ atTop) = (∀ᶠ n in atTop, u n ∈ U) := by
  rfl

example {X : Type*} [TopologicalSpace X] (u : ℕ → X) (x : X) :
    Tendsto u atTop (𝓝 x) ↔
      ∀ U : Set X, IsOpen U → x ∈ U → ∀ᶠ n in atTop, u n ∈ U := by
  exact tendsto_nhds

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} :
    ContinuousAt f x = Tendsto f (𝓝 x) (𝓝 (f x)) := by
  rfl

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} :
    Continuous f ↔ ∀ x, Tendsto f (𝓝 x) (𝓝 (f x)) := by
  simpa [ContinuousAt] using (continuous_iff_continuousAt (f := f))

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  exact continuous_def

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} :
    (∀ x, Tendsto f (𝓝 x) (𝓝 (f x))) ↔
      ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  rw [← continuous_def]
  simpa [ContinuousAt] using (continuous_iff_continuousAt (f := f)).symm

end NeighborhoodFilters

/-
### 演習問題

`Tendsto` の定義を `map` と filter の順序として読み替えてください．

```lean4
example {α β : Type*} (f : α → β) (l : Filter α) (m : Filter β) :
    Tendsto f l m = (map f l ≤ m) := by
  -- 定義そのもの．
  -- 解答例: rfl
  sorry
```
-/

--#--
example {α β : Type*} (f : α → β) (l : Filter α) (m : Filter β) :
    Tendsto f l m = (map f l ≤ m) := by
  -- 定義そのもの．
  -- 解答例: rfl
  sorry
--#--

/-
---
## 連続性の基本 API

前節では，`Tendsto`，`𝓝 x`，開集合の逆像による連続性を数式で読みました．
ここからは，それらを Lean で使うときの名前を確認します．

関数 `f : X → Y` の大域的な連続性は `Continuous f`，
点 `x` での連続性は `ContinuousAt f x`，
集合 `s` 上での連続性は `ContinuousOn f s` です．

この節では定義をもう一度展開するのではなく，よく使う読み替えと操作だけを確認します．

* `rfl`: `ContinuousAt f x` を `Tendsto f (𝓝 x) (𝓝 (f x))` と見る．
* `continuousAt_def`: 点での連続性を近傍の逆像条件として見る．
* `tendsto_nhds`: 終域側が `𝓝 y` の `Tendsto` を開集合で読む．
* `hf.continuousAt`: 大域的連続性から点での連続性を得る．
* `hg.comp hf`: 連続写像の合成が連続であることを使う．

ここで `Continuous.comp` は，`Continuous` の field ではなく，
連続写像の合成が連続であることを述べる定理です．
`hg.comp hf` のように書くとメソッドのように見えますが，
Lean では名前空間 `Continuous` にある定理をドット notation で適用している，と読むとよいです．
一方，`Continuous` の定義の中で宣言されている成分，たとえば開集合の逆像が開集合であることを表す成分は field です．
-/

#check Continuous
#check ContinuousAt
#check ContinuousOn
#check continuousAt_def
#check tendsto_nhds
#check Continuous.isOpen_preimage
#check Continuous.comp

section Continuity

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

example {f : X → Y} {x : X} :
    ContinuousAt f x = Tendsto f (𝓝 x) (𝓝 (f x)) := by
  rfl

example {f : X → Y} {x : X} :
    ContinuousAt f x ↔ ∀ A ∈ 𝓝 (f x), f ⁻¹' A ∈ 𝓝 x := by
  exact continuousAt_def

example {α : Type*} {f : α → Y} {l : Filter α} {y : Y} :
    Tendsto f l (𝓝 y) ↔ ∀ s : Set Y, IsOpen s → y ∈ s → f ⁻¹' s ∈ l := by
  exact tendsto_nhds

example {f : X → Y} (hf : Continuous f) (x : X) : ContinuousAt f x := by
  exact hf.continuousAt

example {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => g (f x) := by
  exact hg.comp hf

end Continuity

/-
---
## 具体的な極限計算

実数列 $a_n$ が $+\infty$ に発散することは，Lean では

```lean4
Tendsto a atTop atTop
```

と書きます．

たとえば，自然数を実数に埋め込んだ列 $n \mapsto n$ は `atTop` に収束します．

具体的な極限計算では，次の 2 つを分けると読みやすくなります．

* `Continuous.tendsto` などで，まず `Tendsto` の証明を作る．
* 終点の値の計算は `calc` で段階的に書く．

`calc` は，等式や不等式を紙の計算に近い形で並べるための構文です．
`Tendsto` そのものを `calc` で示すというより，
`𝓝 ((3 : ℝ)^2 + 1)` を `𝓝 10` に直すような小さな計算に使うと効果的です．
-/

section ConcreteLimits

example : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
  exact tendsto_natCast_atTop_atTop

/-
一点での関数の極限は，始域側を `𝓝 a`，終域側を `𝓝 b` として

```lean4
Tendsto f (𝓝 a) (𝓝 b)
```

と書きます．

以下は $\lim_{x \to 2} (x+3) = 5$ です．
`Continuous.tendsto` は，連続性からその点での極限を取り出す補題です．
最後に，`2 + 3 = 5` という数値計算を `calc` で明示します．
-/

example : Tendsto (fun x : ℝ => x + 3) (𝓝 2) (𝓝 5) := by
  have hlim :
      Tendsto (fun x : ℝ => x + 3) (𝓝 2) (𝓝 ((2 : ℝ) + 3)) :=
    ((by continuity : Continuous fun x : ℝ => x + 3).tendsto (2 : ℝ))
  have hval : (2 : ℝ) + 3 = 5 := by
    calc
      (2 : ℝ) + 3 = (5 : ℝ) := by norm_num
      _ = 5 := by rfl
  simpa [hval] using hlim

/-
上の例では，連続性から得られる極限はまず

```lean4
Tendsto (fun x : ℝ => x + 3) (𝓝 2) (𝓝 (2 + 3))
```

という形です．
一方，示したいゴールは終域側が `𝓝 5` です．
そこで，まずこの極限を `hlim` として保存し，値の計算

```lean4
(2 : ℝ) + 3 = 5
```

を `hval` として別に示します．
最後の `simpa [hval] using hlim` は，`hlim` の終域側の `𝓝 (2 + 3)` を
`𝓝 5` に書き換えています．
-/

/-
同じ方針で，多項式や初等関数の極限も計算できます．
次は $\lim_{x \to 3} (x^2+1) = 10$ と
$\lim_{x \to 0}(\sin x + x^2)=0$ です．
-/

example : Tendsto (fun x : ℝ => x ^ 2 + 1) (𝓝 3) (𝓝 10) := by
  have hlim :
      Tendsto (fun x : ℝ => x ^ 2 + 1) (𝓝 3) (𝓝 ((3 : ℝ) ^ 2 + 1)) :=
    ((by continuity : Continuous fun x : ℝ => x ^ 2 + 1).tendsto (3 : ℝ))
  have hval : (3 : ℝ) ^ 2 + 1 = 10 := by
    calc
      (3 : ℝ) ^ 2 + 1 = (9 : ℝ) + 1 := by norm_num
      _ = 10 := by norm_num
  simpa [hval] using hlim

/-
### 収束先の値を明示しない方法

収束先の値をまだ計算したくないときは，`𝓝 10` のように数値を明示せず，
`𝓝 (f a)` の形で書けます．
たとえば次の例は，$\lim_{x \to 3}(x^2+1)$ の値を `10` まで計算せず，
単に「点 `3` における関数値」へ収束する，という形で述べています．
-/

example :
    Tendsto (fun x : ℝ => x ^ 2 + 1) (𝓝 3)
      (𝓝 ((fun x : ℝ => x ^ 2 + 1) 3)) := by
  exact ((by continuity : Continuous fun x : ℝ => x ^ 2 + 1).tendsto (3 : ℝ))

/-
より一般に，収束先の値そのものを命題の外に出したいなら，
存在命題として

```lean4
∃ y : ℝ, Tendsto f (𝓝 a) (𝓝 y)
```

と書けます．
この場合，証明の中では `refine ⟨..., ?_⟩` によって候補となる値を与えます．
-/

example :
    ∃ y : ℝ, Tendsto (fun x : ℝ => x ^ 2 + 1) (𝓝 3) (𝓝 y) := by
  refine ⟨(fun x : ℝ => x ^ 2 + 1) 3, ?_⟩
  exact ((by continuity : Continuous fun x : ℝ => x ^ 2 + 1).tendsto (3 : ℝ))

/-
一方で，statement に直接 `𝓝 _` と書いて収束先を完全に空欄にする方法は，
通常はうまくいきません．

```lean4
-- これは基本的には失敗します．
-- example : Tendsto (fun x : ℝ => x ^ 2 + 1) (𝓝 3) (𝓝 _) := by
--   exact ((by continuity : Continuous fun x : ℝ => x ^ 2 + 1).tendsto (3 : ℝ))
```

`example : ...` の型は証明本体を読む前に確定されるため，
証明本体から `_` の中身を推論することはできないからです．
値を計算したくない場合は，まず `𝓝 (f a)` の形で書くのが実用的です．
-/

example : Tendsto (fun x : ℝ => Real.sin x + x ^ 2) (𝓝 0) (𝓝 0) := by
  simpa using ((by continuity : Continuous fun x : ℝ => Real.sin x + x ^ 2).tendsto (0 : ℝ))

/-
無限遠での極限も同じ `Tendsto` です．
次は $\lim_{x \to +\infty} 1/x = 0$ です．
ここでは始域側のフィルターが `atTop`，終域側のフィルターが `𝓝 0` になっています．
-/

example : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
  simpa [one_div] using
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))

end ConcreteLimits

/-
---
## 具体的な連続性計算

実数上の初等関数の連続性は，`continuity` tactic で証明できることが多いです．
失敗した場合は，`Continuous.add`，`Continuous.mul`，`Continuous.comp` などの補題を明示的に使います．

式が長くなる場合は，1 行で全部を書くよりも，中間事実に名前を付けると読みやすくなります．
たとえば分数関数では，分子の連続性，分母の連続性，分母が 0 でないことを別々の `have` にします．
数値計算や式変形が長い場合は，前節と同じようにその部分だけ `calc` に切り出せます．
-/

section ConcreteContinuity

example : Continuous fun x : ℝ => x ^ 2 + 1 := by
  continuity

example : ContinuousAt (fun x : ℝ => Real.sin x + x ^ 2) (0 : ℝ) := by
  simpa using
    (Real.continuous_sin.continuousAt.add
      ((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).pow 2))

/-
上の `ContinuousAt` の例では，`Real.continuous_sin`，`continuousAt_id`，
`.pow`，`.add` を手で組み合わせています．
大域的な連続性なら，同じ組み合わせを `continuity` に任せられることも多いです．
たとえば，$x \mapsto \sin x + x^2$ は次のように証明できます．
-/

example : Continuous fun x : ℝ => Real.sin x + x ^ 2 := by
  continuity

/-
分母を持つ関数では，分母が 0 でないことが必要です．
一点での連続性なら，その点で分母が 0 でないことを示せば十分です．
次は $x=0$ における

$$
(x^2+1)/(x+3)
$$

の連続性です．
-/

example : ContinuousAt (fun x : ℝ => (x ^ 2 + 1) / (x + 3)) 0 := by
  have hnum : ContinuousAt (fun x : ℝ => x ^ 2 + 1) 0 :=
    ((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).pow 2).add continuousAt_const
  have hden : ContinuousAt (fun x : ℝ => x + 3) 0 :=
    (continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).add continuousAt_const
  have hden0 : (0 : ℝ) + 3 ≠ 0 := by
    norm_num
  exact hnum.div hden hden0

/-
大域的な連続性では，すべての点で分母が 0 でないことを示します．
次の例では $x^2+2>0$ なので分母は 0 になりません．
-/

example : Continuous fun x : ℝ => (x ^ 2 + 1) / (x ^ 2 + 2) := by
  have hnum : Continuous fun x : ℝ => x ^ 2 + 1 :=
    ((continuous_id : Continuous fun x : ℝ => x).pow 2).add continuous_const
  have hden : Continuous fun x : ℝ => x ^ 2 + 2 :=
    ((continuous_id : Continuous fun x : ℝ => x).pow 2).add continuous_const
  have hden0 : ∀ x : ℝ, x ^ 2 + 2 ≠ 0 := by
    intro x
    positivity
  exact hnum.div hden hden0

end ConcreteContinuity

/-
### 演習問題

1. 開集合の連続写像による逆像が開集合であることを示してください．

    ```lean4
    example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
        {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) :
        IsOpen (f ⁻¹' U) := by
      -- `hU.preimage hf` を試す．
      -- 解答例: exact hU.preimage hf
      sorry
    ```

2. 閉集合の連続写像による逆像が閉集合であることを示してください．

    ```lean4
    example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
        {f : X → Y} (hf : Continuous f) {C : Set Y} (hC : IsClosed C) :
        IsClosed (f ⁻¹' C) := by
      -- `hC.preimage hf` を試す．
      -- 解答例: exact hC.preimage hf
      sorry
    ```

3. 実数値連続関数 `f g : X → ℝ` について，集合 `{x | f x ≤ g x}` が閉集合であることを示してください．

    ```lean4
    example {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
        (hf : Continuous f) (hg : Continuous g) :
        IsClosed {x : X | f x ≤ g x} := by
      -- `isClosed_le hf hg` を調べる．
      -- 解答例: exact isClosed_le hf hg
      sorry
    ```

4. `{x | f x < g x}` が開集合であることを調べてください．

    ```lean4
    example {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
        (hf : Continuous f) (hg : Continuous g) :
        IsOpen {x : X | f x < g x} := by
      -- `isOpen_lt hf hg` を調べる．
      -- 解答例: exact isOpen_lt hf hg
      sorry
    ```

5. `ContinuousAt` が `Tendsto` であることを確認してください．

    ```lean4
    example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
        {f : X → Y} {x : X} :
        ContinuousAt f x = Tendsto f (𝓝 x) (𝓝 (f x)) := by
      -- ヒント: `rfl`
      -- 解答例: rfl
      sorry
    ```

-/

--#--
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) :
    IsOpen (f ⁻¹' U) := by
  -- `hU.preimage hf` を試す．
  -- 解答例: exact hU.preimage hf
  sorry

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {C : Set Y} (hC : IsClosed C) :
    IsClosed (f ⁻¹' C) := by
  -- `hC.preimage hf` を試す．
  -- 解答例: exact hC.preimage hf
  sorry

example {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    IsClosed {x : X | f x ≤ g x} := by
  -- `isClosed_le hf hg` を調べる．
  -- 解答例: exact isClosed_le hf hg
  sorry

example {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    IsOpen {x : X | f x < g x} := by
  -- `isOpen_lt hf hg` を調べる．
  -- 解答例: exact isOpen_lt hf hg
  sorry

#check ContinuousAt

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} :
    ContinuousAt f x = Tendsto f (𝓝 x) (𝓝 (f x)) := by
  -- ヒント: `rfl`
  -- 解答例: rfl
  sorry
--#--

/-
---
## 距離空間での読み替え

距離空間や擬距離空間では，`dist x y`，開球 `Metric.ball x ε`，閉球 `Metric.closedBall x ε` などを使います．
距離空間は位相空間構造を誘導するため，距離の話から `IsOpen` や `Continuous` の話へ移れます．
また `ContinuousAt` のフィルターによる定義は，距離空間では通常の `ε`-`δ` 条件と同値になります．
-/

#check PseudoMetricSpace
#check Metric.ball
#check Metric.closedBall
#check dist
#check Metric.continuousAt_iff

section MetricSpaces

open Metric

variable {X : Type*} [PseudoMetricSpace X]

example (x : X) : dist x x = 0 := by
  simp

example (x y : X) : 0 ≤ dist x y := by
  exact dist_nonneg

example (x : X) (ε : ℝ) (hε : 0 < ε) : x ∈ Metric.ball x ε := by
  simpa [Metric.mem_ball] using hε

example (x : X) (ε : ℝ) : IsOpen (Metric.ball x ε) := by
  exact Metric.isOpen_ball

end MetricSpaces

section MetricContinuity

example {f : ℝ → ℝ} {a : ℝ} :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : ℝ⦄,
      dist x a < δ → dist (f x) (f a) < ε := by
  exact Metric.continuousAt_iff

example : ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : ℝ⦄,
    dist x 3 < δ → dist (x + 1) ((3 : ℝ) + 1) < ε := by
  have h : ContinuousAt (fun y : ℝ => y + 1) (3 : ℝ) := by
    exact (continuousAt_id : ContinuousAt (fun y : ℝ => y) 3).add continuousAt_const
  exact Metric.continuousAt_iff.mp h

end MetricContinuity

/-
`Metric.ball x ε` は集合です．
したがって `x ∈ Metric.ball x ε` や `IsOpen (Metric.ball x ε)` のように，集合に関する命題として扱えます．

`Metric.continuousAt_iff` を使うと，具体的な関数の連続性から
`ε`-`δ` 条件を取り出せます．
上の例は $x \mapsto x+1$ が $x=3$ で連続であることを，
距離による条件として読み替えています．

ここに現れる `∀ ⦃x : ℝ⦄, ...` の `⦃x : ℝ⦄` は strict implicit binder です．
`x` 自体は普通の実数の点ですが，定理を使うときには明示的に渡さず，
後続の仮定 `dist x a < δ` などから Lean が推論します．
たとえば `h : ∀ ⦃x : ℝ⦄, dist x a < δ → ...` があるとき，
`h hx` のように書くと，`hx` の型から `x` が推論されます．
構文としては `{{x : ℝ}}` と入力でき，表示上は `⦃x : ℝ⦄` になります．
括弧の種類の一般的な説明は基礎編 Chapter 02 の `variable` と引数の節で扱いました．
-/

/-
### 演習問題

1. 距離空間で，開球が開集合であることをもう一度証明してください．

    ```lean4
    example {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) :
        IsOpen (Metric.ball x r) := by
      -- `Metric.isOpen_ball`．
      -- 解答例: exact Metric.isOpen_ball
      sorry
    ```

2. 距離空間で，`ContinuousAt` が `ε`-`δ` 条件と同値であることを確認してください．

    ```lean4
    example {f : ℝ → ℝ} {a : ℝ} :
        ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : ℝ⦄,
          dist x a < δ → dist (f x) (f a) < ε := by
      -- ヒント: `exact Metric.continuousAt_iff`
      -- 解答例: exact Metric.continuousAt_iff
      sorry
    ```
-/

--#--
example {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) :
    IsOpen (Metric.ball x r) := by
  -- `Metric.isOpen_ball`．
  -- 解答例: exact Metric.isOpen_ball
  sorry

example {f : ℝ → ℝ} {a : ℝ} :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : ℝ⦄,
      dist x a < δ → dist (f x) (f a) < ε := by
  -- ヒント: `exact Metric.continuousAt_iff`
  -- 解答例: exact Metric.continuousAt_iff
  sorry
--#--

/-
---
## コンパクト性と連結性

ここまでの `IsOpen`，`IsClosed`，`Continuous` を使って，位相的な性質を扱います．
コンパクト性は `IsCompact s` で表されます．
これは `s : Set X` に対する述語です．
閉集合や連続写像との相互作用は，解析や微分積分で頻繁に使います．

連結性について，Mathlib では空集合も許した連結性を `IsPreconnected s` と呼びます．
非空性まで含めた通常の連結集合は `IsConnected s` です．
中間値の定理の証明で本質的に使うのは「2 つの閉集合による分離ができない」という性質なので，
`IsPreconnected` が主役になります．
-/

#check IsCompact
#check IsCompact.image
#check IsClosed
#check IsPreconnected
#check IsConnected
#check isPreconnected_Icc
#check IsPreconnected.intermediate_value
#check intermediate_value_Icc
#check intermediate_value_Icc'

section CompactnessAndConnectedness

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {s : Set X} {f : X → Y}

example (hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s) := by
  exact hs.image hf

example : IsPreconnected (Icc (0 : ℝ) 1) := by
  exact isPreconnected_Icc

end CompactnessAndConnectedness

/-
`IsCompact.image` は，コンパクト集合の連続像がコンパクトであることを述べます．
`isPreconnected_Icc` は，閉区間 `Icc a b` が preconnected であるという定理です．
`IsPreconnected.intermediate_value` は，preconnected な集合上の連続関数について，
端点値の間の閉区間が像に含まれることを述べます．
閉区間に特化した使いやすい形が `intermediate_value_Icc` です．
-/

/-
---
## 長めの例: 連続関数の零点集合は閉集合

位相の典型的な主張として，連続関数 `f : X → ℝ` の零点集合

```text
{x | f x = 0}
```

は閉集合です．
紙の証明では「`{0}` は `ℝ` の閉集合で，零点集合はその逆像である」と説明します．
Lean でも同じ構造で証明します．
-/

def zeroSet {X : Type*} (f : X → ℝ) : Set X :=
  {x | f x = 0}

section ZeroSet

variable {X : Type*} [TopologicalSpace X]
variable {f : X → ℝ}

example (hf : Continuous f) : IsClosed (zeroSet f) := by
  simpa [zeroSet] using isClosed_singleton.preimage hf

example (hf : Continuous f) (c : ℝ) : IsClosed {x : X | f x = c} := by
  simpa using isClosed_eq hf continuous_const

end ZeroSet

/-
2 つ目の例は，level set `{x | f x = c}` が閉集合であることを示しています．
証明では `{x | f x = c}` を `{x | f x - c = 0}` と見て，
連続関数 `x ↦ f x - c` の零点集合として扱っています．

`simpa` は，このような表現の差を整理するためによく使います．
-/

/-
### 演習問題

`zeroSet` を使わずに `{x | f x = 0}` が閉集合であることを直接証明してください．

```lean4
example {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) :
    IsClosed {x : X | f x = 0} := by
  -- `isClosed_eq hf continuous_const` を使う．
  -- 解答例: simpa using isClosed_eq hf continuous_const
  sorry
```
-/

--#--
example {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) :
    IsClosed {x : X | f x = 0} := by
  -- `isClosed_eq hf continuous_const` を使う．
  -- 解答例: simpa using isClosed_eq hf continuous_const
  sorry
--#--

/-
---
## 長めの例: コンパクト集合の連続像

コンパクト集合の連続像はコンパクトです．
さらに，値域が Hausdorff 空間ならコンパクト集合は閉集合です．
したがって，Hausdorff 空間への連続写像では，コンパクト集合の像は閉集合になります．
-/

section CompactImage

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
variable {s : Set X} {f : X → Y}

example (hs : IsCompact s) (hf : Continuous f) : IsClosed (f '' s) := by
  exact (hs.image hf).isClosed

end CompactImage

/-
ここで `[T2Space Y]` は，`Y` が Hausdorff 空間であるという型クラス仮定です．
定理 `IsCompact.isClosed` は一般の位相空間では成り立たず，Hausdorff 条件を要求します．
型クラス仮定として必要な位相的条件が明示されるのは，Mathlib の位相の読み方で重要です．
-/

/-
---
## 長めの例: 中間値の定理

位相のもう 1 つの典型例として，中間値の定理を見ます．

紙の数学では「閉区間 $[a,b]$ は連結であり，連続写像は連結集合を連結集合へ送る．
したがって実数値連続関数の像は区間になり，端点値の間の値をすべて取る」と説明します．
数式で書けば，連結な集合 $s$ 上の連続関数 $f : X \to \mathbb R$ について，
$a,b \in s$ かつ $f(a) \le f(b)$ なら

$$
[f(a), f(b)] \subseteq f(s)
$$

です．
つまり，

$$
f(a) \le c \le f(b)
\quad\Longrightarrow\quad
\exists x \in s,\ f(x) = c.
$$

閉区間版では，$a \le b$ かつ $f$ が $[a,b]$ 上連続であれば，

$$
f(a) \le c \le f(b)
\quad\Longrightarrow\quad
\exists x \in [a,b],\ f(x) = c
$$

となります．
端点値の大小が逆なら，$f(b) \le c \le f(a)$ の形で同じ主張を使います．
前の節で見た `IsPreconnected` と `intermediate_value_Icc` を使うと，
この議論をそのまま Lean で表せます．
-/

section IntermediateValueTheorem

example {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsPreconnected s)
    {a b : X} (ha : a ∈ s) (hb : b ∈ s) {f : X → ℝ}
    (hf : ContinuousOn f s) :
    Icc (f a) (f b) ⊆ f '' s := by
  exact hs.intermediate_value ha hb hf

example {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsPreconnected s)
    {a b : X} (ha : a ∈ s) (hb : b ∈ s) {f : X → ℝ}
    (hf : ContinuousOn f s) {c : ℝ} (hc : c ∈ Icc (f a) (f b)) :
    ∃ x ∈ s, f x = c := by
  rcases hs.intermediate_value ha hb hf hc with ⟨x, hx, hfx⟩
  exact ⟨x, hx, hfx⟩

example {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (ha : f a ≤ c) (hb : c ≤ f b) :
    ∃ x ∈ Icc a b, f x = c := by
  exact intermediate_value_Icc hab hf ⟨ha, hb⟩

example {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (ha : f b ≤ c) (hb : c ≤ f a) :
    ∃ x ∈ Icc a b, f x = c := by
  exact intermediate_value_Icc' hab hf ⟨ha, hb⟩

end IntermediateValueTheorem

/-
最後の 2 つの例は，端点値の順序に応じて定理を使い分けています．
`intermediate_value_Icc` は `f a ≤ c ≤ f b` の場合，
`intermediate_value_Icc'` は `f b ≤ c ≤ f a` の場合です．

具体例として，$x^2$ が $[0,2]$ 上で値 $2$ を取ることを示します．
これは平方根の存在そのものではありませんが，中間値の定理の使い方としては典型的です．
ここで使っている数学的な事実は，

$$
0^2 \le 2 \le 2^2
\quad\Longrightarrow\quad
\exists x \in [0,2],\ x^2 = 2
$$

です．
-/

example : ∃ x ∈ Icc (0 : ℝ) 2, x ^ 2 = 2 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 2) (Icc (0 : ℝ) 2) := by
    exact ((continuous_id : Continuous fun x : ℝ => x).pow 2).continuousOn
  have h2 : (2 : ℝ) ∈ Icc ((fun x : ℝ => x ^ 2) 0) ((fun x : ℝ => x ^ 2) 2) := by
    norm_num
  simpa using intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2) hcont h2

/-
### Mathlib の証明の読み方

Mathlib の本体では，まず次のような少し強い形を証明しています．

数学的には，連続関数 $f,g : X \to \mathbb R$ と点 $a,b \in X$ について

$$
f(a) \le g(a),\qquad g(b) \le f(b)
$$

が成り立つなら，

$$
\exists x,\ f(x) = g(x)
$$

を示す形です．

```lean4
intermediate_value_univ₂ :
  Continuous f → Continuous g →
  f a ≤ g a → g b ≤ f b → ∃ x, f x = g x
```

証明の核だけを抜き出すと次の部分です．

```lean4
obtain ⟨x, _, hfg, hgf⟩ :
    (univ ∩ { x | f x ≤ g x ∧ g x ≤ f x }).Nonempty :=
  isPreconnected_closed_iff.1 PreconnectedSpace.isPreconnected_univ _ _
    (isClosed_le hf hg) (isClosed_le hg hf)
    (fun _ _ => le_total _ _) ⟨a, trivial, ha⟩ ⟨b, trivial, hb⟩
exact ⟨x, le_antisymm hfg hgf⟩
```

ここで考える閉集合は

```lean4
{x | f x ≤ g x},   {x | g x ≤ f x}
```

です．
数式では

$$
A = \{x \mid f(x) \le g(x)\},\qquad
B = \{x \mid g(x) \le f(x)\}
$$

と置いています．
`isClosed_le hf hg` によって，連続関数の大小関係で定まる集合が閉集合であることが分かります．
また任意の点 `x` では `le_total (f x) (g x)` により，少なくともどちらか一方の閉集合に入ります．
つまり

$$
X = A \cup B
$$

です．
端点の仮定 `f a ≤ g a` と `g b ≤ f b` は，それぞれの閉集合が空でないことを与えます．

連結性はここで使われます．
`isPreconnected_closed_iff` は，preconnected な集合を 2 つの閉集合で覆い，
両方に点があるなら，2 つの閉集合の交わりにも点がある，という形の補題です．
数式では，

$$
A \ne \emptyset,\quad B \ne \emptyset,\quad X = A \cup B
\quad\Longrightarrow\quad
A \cap B \ne \emptyset
$$

という使い方です．
その交点の点 `x` では

```lean4
f x ≤ g x,   g x ≤ f x
```

が同時に成り立つので，`le_antisymm` から `f x = g x` が出ます．
すなわち

$$
x \in A \cap B
\quad\Longrightarrow\quad
f(x) \le g(x)\ \text{and}\ g(x) \le f(x)
\quad\Longrightarrow\quad
f(x) = g(x).
$$

次に，集合 `s` 上の定理

```lean4
IsPreconnected.intermediate_value₂
```

は，`s` を部分型として見て全空間版を適用します．
このとき `Subtype.preconnectedSpace hs` が「preconnected な集合 `s` は，
部分型として preconnected な空間になる」ことを与え，
`continuousOn_iff_continuous_restrict` が `ContinuousOn f s` を
部分型上の `Continuous` に読み替えます．

最後に，通常の中間値の定理

```lean4
IsPreconnected.intermediate_value
```

は，2 つ目の関数 `g` として定数関数 `fun _ => c` を取った特殊ケースです．
閉区間版

```lean4
intermediate_value_Icc
```

はさらに `s = Icc a b` とし，`isPreconnected_Icc`，
`left_mem_Icc.2 hab`，`right_mem_Icc.2 hab` を渡したものです．
実際の定理の本体はほぼ次の 1 行です．

```lean4
isPreconnected_Icc.intermediate_value (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hf
```

つまり Mathlib の中間値の定理は，

1. 連続関数の大小で定まる閉集合を作る．
2. preconnected 性から，2 つの閉集合の交点を得る．
3. 交点では両向きの不等式があるので等式にする．
4. 一般の集合から閉区間へ特殊化する．

という流れで証明されています．
-/

/-
---
## まとめ

Mathlib の位相では，極限を直接 `ε`-`δ` で定義するのではなく，フィルター `Tendsto` を基礎にします．
開集合・閉集合・閉包・内部は `Set` 上の述語や操作として扱われます．
距離空間では `Metric.ball` や `dist` を使い，連続性は `Continuous`，`ContinuousAt`，`ContinuousOn` で表します．
特に `ContinuousAt f x` は `Tendsto f (𝓝 x) (𝓝 (f x))` なので，点での連続性もフィルターの極限として読めます．
中間値の定理では，閉区間 `Icc a b` が `IsPreconnected` であることと，
連続関数の大小関係で定まる閉集合が閉じていることを組み合わせます．

微分と積分の章では，これらの位相的な語彙がそのまま使われます．

### 形式化の tips

位相の形式化では，同じ定理が「集合の言葉」「フィルターの言葉」「距離の言葉」で出てきます．
どのレベルで証明するかを選ぶのが重要です．

1. 開集合・閉集合の問題なら `IsOpen`，`IsClosed` を探す．
2. 極限の問題なら `Tendsto` と `𝓝` を読む．
3. 距離空間の問題なら `Metric.ball`，`dist`，`Metric.mem_ball` を使う．
4. 連続性の合成なら `Continuous.comp` または `hg.comp hf` を使う．
5. compactness では，Hausdorff 条件 `[T2Space X]` が必要かを確認する．
6. 中間値の定理では `intermediate_value_Icc` と `intermediate_value_Icc'` を探す．
-/

end PracticeChapter03 --#
