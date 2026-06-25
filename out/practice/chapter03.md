# Chapter 03: 位相

Mathlib における基本的な位相を扱います．

参考:

* Mathematics in Lean, 11. Topology: <https://leanprover-community.github.io/mathematics_in_lean/C11_Topology.html>
* Maths in Lean: Topological, uniform and metric spaces: <https://leanprover-community.github.io/theories/topology.html>

フィルター，距離空間，位相空間，連続性，コンパクト性などが説明されています．

Lean での位相はフィルターに基づいて形式化されています．
フィルターは，数列の極限，関数の極限，無限遠での振る舞い，近傍，ほとんど至る所，などを同じ言葉で扱うための道具です．

```lean
import Mathlib

namespace PracticeChapter03

open Set Filter
open scoped Topology
```

---
## 位相空間

位相空間構造は `TopologicalSpace X` です．
開集合は `IsOpen U`，閉集合は `IsClosed C` と書きます．
`interior`，`closure`，`frontier` なども `Set X` に対する操作です．

```lean
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
```

集合の等式や包含と同じように，位相的な操作も `Set` の補題と組み合わせて使います．
たとえば，`closure_mono` は集合の包含から閉包の包含を得る補題です．

### 演習問題

1. `closure_mono` を使って，`s ⊆ t` なら `closure s ⊆ closure t` を示してください．

    ```lean4
    example {X : Type*} [TopologicalSpace X] {s t : Set X} (hst : s ⊆ t) :
        closure s ⊆ closure t := by
      -- ヒント: `exact closure_mono hst`
      sorry
    ```

2. `interior s ⊆ s` と `s ⊆ closure s` をそれぞれ確認してください．

    ```lean4
    #check interior_subset
    #check subset_closure
    ```

---
## フィルター

`Filter α` は，`α` の部分集合の集まりに閉性条件を入れた構造です．
距離空間での点列の収束を一般化するために使われます．
数学的には，集合 $\alpha$ 上のフィルター $F \subset \mathcal P(\alpha)$ は，$\alpha$ の部分集合からなる族で，次を満たすものです．

* 全体集合 $\alpha$ を含む: $\alpha \in F$
* 空集合 $\emptyset$ を含まない: $\emptyset \notin F$
* 上に閉じている: $U \in F, V \in \mathcal P(\alpha)$ かつ $U \subset V$ なら $V \in F$．
* 共通部分演算で閉じている: $U,V \in F$ なら $U \cap V \in F$．

ただし Lean の `Filter α` は技術的な都合で `∅` を含む退化したフィルターも許します．退化していないこと（真のフィルター）が必要な場面では，`NeBot l` という型クラスを仮定します．

記法 `∀ᶠ x in l, p x` は，「フィルター `l` の意味で十分近い，あるいは十分先の `x` について `p x` が成り立つ」という意味です．
フィルターに慣れていないうちは，「少数の例外を無視して `p x` が成り立つ」と読むとよいです．
どの例外を無視してよいかは，フィルター `l` が決めます．
定義上は，集合 `{x | p x}` がフィルター `l` に属する，という主張です．

たとえば `∀ᶠ n in atTop, p n` は，数列や自然数添字の議論で使われます．
これは「ある番号 `N` 以降のすべての `n` について `p n` が成り立つ」という意味で，有限個の初期項での失敗を無視します．
極限の証明で「十分大きい `n` について」と言う場面は，Lean ではこの形で書くことが多いです．

また `∀ᶠ y in 𝓝 x, p y` は，点 `x` の近くで成り立つ性質を表します．
これは「`x` を含むある近傍のすべての点 `y` について `p y` が成り立つ」という意味です．
連続性や局所的な議論で，「`x` の十分近くでは分母が 0 でない」「`x` の十分近くでは同じ式で表せる」といった主張を書くときに使います．

測度論では `∀ᶠ x in ae μ, p x`，または同じ意味の記法 `∀ᵐ x ∂μ, p x` を使います．
これは「測度 `μ` に関してほとんど至る所 `p x` が成り立つ」という意味です．
失敗する点全体の集合が零測度なら，その例外を無視します．
積分論や確率論では，関数が一点ごとに完全に一致しなくても，零測度集合を除いて一致すれば同じものとして扱いたい場面が多く，そのために `ae μ` が使われます．

代表例は次の通りです．

* `atTop`: 十分大きい値に対応するフィルター．`s ∈ atTop` は，ある境界より先の値がすべて `s` に入ることを意味する．自然数上では「十分大きい `n`」そのもの．
* `𝓝 x`: 点 `x` の近傍フィルター（点 $x$ の近傍全体 $\mathcal N(x)$）．`s ∈ 𝓝 x` は，`x` を含む開集合が `s` に含まれることを意味する．
* `ae μ`: 測度 `μ` に関してほとんど至る所成り立つ，というフィルター．`s ∈ ae μ` は，補集合 `sᶜ` が零測度であることを意味する．

`Tendsto f l m` は，「`x` がフィルター `l` に沿って動くとき，`f x` がフィルター `m` に沿って動く」という意味です．
数列の極限も，関数の一点での極限も，無限遠での極限も，この形で表されます．
定義上は，`f` による `l` の像フィルター `map f l` が `m` より細かい，つまり `map f l ≤ m` であるという条件です．

```lean
#check Filter
#check Tendsto
#check atTop
#check 𝓝
#check Filter.Eventually
#check MeasureTheory.ae_iff
#check MeasureTheory.mem_ae_iff

section Filters

example {α : Type*} {l : Filter α} {p : α → Prop} :
    (∀ᶠ x in l, p x) = ({x | p x} ∈ l) := by
  rfl

example : (∀ᶠ n in (atTop : Filter Nat), 3 ≤ n) := by
  exact eventually_ge_atTop 3

example {X : Type*} [TopologicalSpace X] {x : X} {s : Set X} :
    s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t := by
  exact mem_nhds_iff

example {α β : Type*} {f : α → β} {l : Filter α} {m : Filter β} :
    Tendsto f l m = (map f l ≤ m) := by
  rfl

end Filters
```

### 近傍フィルターによる収束と連続

位相空間における「近い」という情報は，Mathlib では点 `x` の近傍フィルター `𝓝 x` として扱われます．
Mathlib 本体では，近傍フィルターは次のように定義されています．

```lean title=".lake/packages/mathlib/Mathlib/Topology/Defs/Filter.lean"
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s

scoped[Topology] notation "𝓝" => nhds
```

ここで `𝓟 s` は集合 `s` で生成される主フィルターです．
つまり `𝓝 x` は，「`x` を含む開集合」から来る主フィルターをすべて集めたものです．
実際に使うときは，この定義を直接展開するより，次の補題で読む方が便利です．

```lean title=".lake/packages/mathlib/Mathlib/Topology/Neighborhoods.lean"
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t
```

これは，`s` が `x` の近傍であるとは，`s` の中に `x` を含む開集合 `t` があることだ，という通常の定義そのものです．

また `nhds (x) : Filter X` なので，近傍全体は Lean の意味でフィルターです．
すなわち，全体集合を含み，上に閉じており，共通部分で閉じています．
さらに近傍フィルターは退化していないので，`NeBot (𝓝 x)` も成り立ちます．

点列 `u : ℕ → X` が `x` に収束することは，近傍フィルターを使うと

```lean4
Tendsto u atTop (𝓝 x)
```

と書けます．
これは「十分大きい `n` について，`u n` は `x` の任意の近傍に入る」という意味です．
実際，`tendsto_nhds` により，これは次の通常の点列収束の条件と同値です．

```text
任意の開集合 U について，x ∈ U なら，十分大きい n で u n ∈ U
```

証明は次の通りです．
`Tendsto u atTop (𝓝 x)` を展開すると，`x` の任意の近傍 `A` に対して `u ⁻¹' A ∈ atTop` であることです．
特に `x` を含む開集合 `U` は `U ∈ 𝓝 x` なので，十分大きい `n` で `u n ∈ U` です．
逆に，任意の開近傍 `U` について十分先で `u n ∈ U` だとします．
任意の近傍 `A ∈ 𝓝 x` に対し，`mem_nhds_iff` から `x ∈ U` かつ `U ⊆ A` となる開集合 `U` が取れます．
仮定より十分先で `u n ∈ U`，したがって十分先で `u n ∈ A` です．
これが `Tendsto u atTop (𝓝 x)` です．

連続性も同じ言葉で定義されます．
一点 `x` での連続性は，`x` に近い点を `f` で送ると `f x` に近い点になる，という条件です．

```lean title=".lake/packages/mathlib/Mathlib/Topology/Defs/Filter.lean"
def ContinuousAt (f : X → Y) (x : X) :=
  Tendsto f (𝓝 x) (𝓝 (f x))
```

一方，教科書でよく見る大域的な連続性は「開集合の逆像が開集合」として定義されます．
Mathlib では次の補題がこの形を与えます．

```lean title=".lake/packages/mathlib/Mathlib/Topology/Continuous.lean"
theorem continuous_def :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

theorem continuous_iff_continuousAt :
    Continuous f ↔ ∀ x, ContinuousAt f x
```

自然言語で証明すると次のようになります．
まず `f` が各点で近傍フィルターの意味で連続だとします．
`Y` の開集合 `U` を取り，`x ∈ f ⁻¹' U` とします．
すると `f x ∈ U` であり，`U` は開集合なので `U ∈ 𝓝 (f x)` です．
点 `x` での連続性から `f ⁻¹' U ∈ 𝓝 x` です．
したがって `f ⁻¹' U` は各点の近傍であり，開集合です．

逆に，任意の開集合の逆像が開集合だとします．
点 `x` と `f x` の近傍 `A` を取ります．
`mem_nhds_iff` により，`f x ∈ U` かつ `U ⊆ A` となる開集合 `U` が取れます．
仮定より `f ⁻¹' U` は開集合で，しかも `x ∈ f ⁻¹' U` です．
よって `f ⁻¹' U ∈ 𝓝 x` であり，`f ⁻¹' U ⊆ f ⁻¹' A` から `f ⁻¹' A ∈ 𝓝 x` です．
これは `Tendsto f (𝓝 x) (𝓝 (f x))`，すなわち点 `x` での連続性です．

```lean
#check nhds
#check mem_nhds_iff
#check tendsto_nhds
#check continuous_def
#check continuous_iff_continuousAt

section NeighborhoodFilters

example {X : Type*} [TopologicalSpace X] (x : X) : Filter X :=
  𝓝 x

example {X : Type*} [TopologicalSpace X] (x : X) : (univ : Set X) ∈ 𝓝 x := by
  exact univ_mem

example {X : Type*} [TopologicalSpace X] {x : X} {s t : Set X}
    (hs : s ∈ 𝓝 x) (ht : t ∈ 𝓝 x) : s ∩ t ∈ 𝓝 x := by
  exact inter_mem hs ht

example {X : Type*} [TopologicalSpace X] {x : X} {s t : Set X}
    (hs : s ∈ 𝓝 x) (hst : s ⊆ t) : t ∈ 𝓝 x := by
  exact mem_of_superset hs hst

example {X : Type*} [TopologicalSpace X] (x : X) : NeBot (𝓝 x) := by
  infer_instance

def SeqConvergesToByNhds {X : Type*} [TopologicalSpace X] (u : ℕ → X) (x : X) : Prop :=
  Tendsto u atTop (𝓝 x)

example {X : Type*} [TopologicalSpace X] {u : ℕ → X} {U : Set X} :
    (u ⁻¹' U ∈ atTop) = (∀ᶠ n in atTop, u n ∈ U) := by
  rfl

example {X : Type*} [TopologicalSpace X] (u : ℕ → X) (x : X) :
    SeqConvergesToByNhds u x ↔
      ∀ U : Set X, IsOpen U → x ∈ U → ∀ᶠ n in atTop, u n ∈ U := by
  unfold SeqConvergesToByNhds
  exact tendsto_nhds

def ContinuousAtByNhds {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (x : X) : Prop :=
  Tendsto f (𝓝 x) (𝓝 (f x))

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} :
    ContinuousAtByNhds f x = ContinuousAt f x := by
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
```

### 演習問題

`Tendsto` の定義を `map` と filter の順序として読み替えてください．

```lean4
example {α β : Type*} (f : α → β) (l : Filter α) (m : Filter β) :
    Tendsto f l m = (map f l ≤ m) := by
  -- 定義そのもの．
  sorry
```

---
## 収束と連続性

関数 `f : X → Y` の連続性は `Continuous f` です．
一点 `x` での連続性は `ContinuousAt f x`，集合 `s` 上の連続性は `ContinuousOn f s` です．
Mathlib では，一点での連続性がフィルターで定義されています:

```lean title="Mathlib.Topology.Defs"
def ContinuousAt (f : X → Y) (x : X) :=
  Tendsto f (𝓝 x) (𝓝 (f x))
def ContinuousOn (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ContinuousWithinAt f s x
```

これは「`x` に十分近い点を `f` で送ると，`f x` に十分近い点になる」という意味です．
より展開すると，`f x` の任意の近傍 `A` に対して，その逆像 `f ⁻¹' A` が `x` の近傍である，という条件になります．
位相空間の教科書では大域的な連続性を「開集合の逆像が開集合」と定義することが多いですが，
フィルターを使うと点での連続性，数列や関数の極限，無限遠での極限を同じ `Tendsto` の形で扱えます．

距離空間では，この定義は通常の `ε`-`δ` に戻ります．
この読み替えは，後の「距離空間での読み替え」で扱います．

```lean
#check Continuous
#check ContinuousAt
#check ContinuousOn

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
```

### 演習問題

1. 開集合の連続写像による逆像が開集合であることを示してください．

    ```lean4
    example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
        {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) :
        IsOpen (f ⁻¹' U) := by
      -- `hU.preimage hf` を試す．
      sorry
    ```

2. 閉集合の連続写像による逆像が閉集合であることを示してください．

    ```lean4
    example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
        {f : X → Y} (hf : Continuous f) {C : Set Y} (hC : IsClosed C) :
        IsClosed (f ⁻¹' C) := by
      -- `hC.preimage hf` を試す．
      sorry
    ```

3. 実数値連続関数 `f g : X → ℝ` について，集合 `{x | f x ≤ g x}` が閉集合であることを示してください．

    ```lean4
    example {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
        (hf : Continuous f) (hg : Continuous g) :
        IsClosed {x : X | f x ≤ g x} := by
      -- `isClosed_le hf hg` を調べる．
      sorry
    ```

4. `{x | f x < g x}` が開集合であることを調べてください．

    ```lean4
    example {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
        (hf : Continuous f) (hg : Continuous g) :
        IsOpen {x : X | f x < g x} := by
      -- `isOpen_lt hf hg` を調べる．
      sorry
    ```

5. `ContinuousAt` が `Tendsto` であることを確認してください．

    ```lean4
    example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
        {f : X → Y} {x : X} :
        ContinuousAt f x = Tendsto f (𝓝 x) (𝓝 (f x)) := by
      -- ヒント: `rfl`
      sorry
    ```

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

```lean
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
```

`IsCompact.image` は，コンパクト集合の連続像がコンパクトであることを述べます．
`isPreconnected_Icc` は，閉区間 `Icc a b` が preconnected であるという定理です．
`IsPreconnected.intermediate_value` は，preconnected な集合上の連続関数について，
端点値の間の閉区間が像に含まれることを述べます．
閉区間に特化した使いやすい形が `intermediate_value_Icc` です．

---
## 距離空間での読み替え

距離空間や擬距離空間では，`dist x y`，開球 `Metric.ball x ε`，閉球 `Metric.closedBall x ε` などを使います．
距離空間は位相空間構造を誘導するため，距離の話から `IsOpen` や `Continuous` の話へ移れます．
また `ContinuousAt` のフィルターによる定義は，距離空間では通常の `ε`-`δ` 条件と同値になります．

```lean
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
```

`Metric.ball x ε` は集合です．
したがって `x ∈ Metric.ball x ε` や `IsOpen (Metric.ball x ε)` のように，集合に関する命題として扱えます．

`Metric.continuousAt_iff` を使うと，具体的な関数の連続性から
`ε`-`δ` 条件を取り出せます．
上の例は $x \mapsto x+1$ が $x=3$ で連続であることを，
距離による条件として読み替えています．

### 演習問題

1. 距離空間で，開球が開集合であることをもう一度証明してください．

    ```lean4
    example {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) :
        IsOpen (Metric.ball x r) := by
      -- `Metric.isOpen_ball`．
      sorry
    ```

2. 距離空間で，`ContinuousAt` が `ε`-`δ` 条件と同値であることを確認してください．

    ```lean4
    example {f : ℝ → ℝ} {a : ℝ} :
        ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : ℝ⦄,
          dist x a < δ → dist (f x) (f a) < ε := by
      -- ヒント: `exact Metric.continuousAt_iff`
      sorry
    ```

---
## 具体的な極限計算

実数列 $a_n$ が $+\infty$ に発散することは，Lean では

```lean4
Tendsto a atTop atTop
```

と書きます．

たとえば，自然数を実数に埋め込んだ列 $n \mapsto n$ は `atTop` に収束します．

```lean
section ConcreteLimits

example : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
  exact tendsto_natCast_atTop_atTop
```

一点での関数の極限は，始域側を `𝓝 a`，終域側を `𝓝 b` として

```lean4
Tendsto f (𝓝 a) (𝓝 b)
```

と書きます．

以下は $\lim_{x \to 2} (x+3) = 5$ です．
`Continuous.tendsto` は，連続性からその点での極限を取り出す補題です．
最後の `norm_num` は，`2 + 3 = 5` の数値計算を処理しています．

```lean
example : Tendsto (fun x : ℝ => x + 3) (𝓝 2) (𝓝 5) := by
  convert (((continuous_id : Continuous fun x : ℝ => x).add
    (continuous_const : Continuous fun _ : ℝ => (3 : ℝ))).tendsto (2 : ℝ)) using 1
  norm_num
```

ここで使っている `convert` は，手元にある定理の結論が現在のゴールと「ほとんど同じ」だが，
一部の式だけがまだ一致していないときに便利な tactic です．

上の例では，連続性から得られる極限はまず

```lean4
Tendsto (fun x : ℝ => x + 3) (𝓝 2) (𝓝 (2 + 3))
```

という形です．
一方，示したいゴールは終域側が `𝓝 5` です．
`convert ... using 1` は，この 2 つの主張を対応させたうえで，
残った差分 `2 + 3 = 5` を新しいゴールとして残します．
最後の `norm_num` がその数値計算を閉じています．

同じ方針で，多項式や初等関数の極限も計算できます．
次は $\lim_{x \to 3} (x^2+1) = 10$ と
$\lim_{x \to 0}(\sin x + x^2)=0$ です．

```lean
example : Tendsto (fun x : ℝ => x ^ 2 + 1) (𝓝 3) (𝓝 10) := by
  convert ((by continuity : Continuous fun x : ℝ => x ^ 2 + 1).tendsto (3 : ℝ)) using 1
  norm_num

example : Tendsto (fun x : ℝ => Real.sin x + x ^ 2) (𝓝 0) (𝓝 0) := by
  simpa using ((by continuity : Continuous fun x : ℝ => Real.sin x + x ^ 2).tendsto (0 : ℝ))
```

無限遠での極限も同じ `Tendsto` です．
次は $\lim_{x \to +\infty} 1/x = 0$ です．
ここでは始域側のフィルターが `atTop`，終域側のフィルターが `𝓝 0` になっています．

```lean
example : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
  simpa [one_div] using
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))

end ConcreteLimits
```

---
## 具体的な連続性計算

実数上の初等関数の連続性は，`continuity` tactic で証明できることが多いです．
失敗した場合は，`Continuous.add`，`Continuous.mul`，`Continuous.comp` などの補題を明示的に使います．

```lean
section ConcreteContinuity

example : Continuous fun x : ℝ => x ^ 2 + 1 := by
  continuity

example : ContinuousAt (fun x : ℝ => Real.sin x + x ^ 2) (0 : ℝ) := by
  simpa using
    (Real.continuous_sin.continuousAt.add
      ((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).pow 2))
```

具体的な関数の連続性は，初等関数・四則演算・合成に関する補題を組み合わせて示します．
`continuity` tactic はこの組み合わせを自動で行います．
たとえば，$x \mapsto \sin x + x^2$ は実数上連続です．

```lean
example : Continuous fun x : ℝ => Real.sin x + x ^ 2 := by
  continuity
```

分母を持つ関数では，分母が 0 でないことが必要です．
一点での連続性なら，その点で分母が 0 でないことを示せば十分です．
次は $x=0$ における

```text
(x^2+1)/(x+3)
```

の連続性です．

```lean
example : ContinuousAt (fun x : ℝ => (x ^ 2 + 1) / (x + 3)) 0 := by
  exact (((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).pow 2).add
    continuousAt_const).div
    ((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).add continuousAt_const)
    (by norm_num)
```

大域的な連続性では，すべての点で分母が 0 でないことを示します．
次の例では $x^2+2>0$ なので分母は 0 になりません．

```lean
example : Continuous fun x : ℝ => (x ^ 2 + 1) / (x ^ 2 + 2) := by
  exact (((continuous_id : Continuous fun x : ℝ => x).pow 2).add continuous_const).div
    (((continuous_id : Continuous fun x : ℝ => x).pow 2).add continuous_const)
    (by
      intro x
      positivity)

end ConcreteContinuity
```

---
## 長めの例: 連続関数の零点集合は閉集合

位相の典型的な主張として，連続関数 `f : X → ℝ` の零点集合

```text
{x | f x = 0}
```

は閉集合です．
紙の証明では「`{0}` は `ℝ` の閉集合で，零点集合はその逆像である」と説明します．
Lean でも同じ構造で証明します．

```lean
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
```

2 つ目の例は，level set `{x | f x = c}` が閉集合であることを示しています．
証明では `{x | f x = c}` を `{x | f x - c = 0}` と見て，
連続関数 `x ↦ f x - c` の零点集合として扱っています．

`simpa` は，このような表現の差を整理するためによく使います．

### 演習問題

`zeroSet` を使わずに `{x | f x = 0}` が閉集合であることを直接証明してください．

```lean4
example {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) :
    IsClosed {x : X | f x = 0} := by
  -- `isClosed_eq hf continuous_const` を使う．
  sorry
```

---
## 長めの例: コンパクト集合の連続像

コンパクト集合の連続像はコンパクトです．
さらに，値域が Hausdorff 空間ならコンパクト集合は閉集合です．
したがって，Hausdorff 空間への連続写像では，コンパクト集合の像は閉集合になります．

```lean
section CompactImage

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
variable {s : Set X} {f : X → Y}

example (hs : IsCompact s) (hf : Continuous f) : IsClosed (f '' s) := by
  exact (hs.image hf).isClosed

end CompactImage
```

ここで `[T2Space Y]` は，`Y` が Hausdorff 空間であるという型クラス仮定です．
定理 `IsCompact.isClosed` は一般の位相空間では成り立たず，Hausdorff 条件を要求します．
型クラス仮定として必要な位相的条件が明示されるのは，Mathlib の位相の読み方で重要です．

---
## 長めの例: 中間値の定理

位相のもう 1 つの典型例として，中間値の定理を見ます．

紙の数学では「閉区間 $[a,b]$ は連結であり，連続写像は連結集合を連結集合へ送る．
したがって実数値連続関数の像は区間になり，端点値の間の値をすべて取る」と説明します．
前の節で見た `IsPreconnected` と `intermediate_value_Icc` を使うと，
この議論をそのまま Lean で表せます．

```lean
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
```

最後の 2 つの例は，端点値の順序に応じて定理を使い分けています．
`intermediate_value_Icc` は `f a ≤ c ≤ f b` の場合，
`intermediate_value_Icc'` は `f b ≤ c ≤ f a` の場合です．

具体例として，$x^2$ が $[0,2]$ 上で値 $2$ を取ることを示します．
これは平方根の存在そのものではありませんが，中間値の定理の使い方としては典型的です．

```lean
example : ∃ x ∈ Icc (0 : ℝ) 2, x ^ 2 = 2 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 2) (Icc (0 : ℝ) 2) := by
    exact ((continuous_id : Continuous fun x : ℝ => x).pow 2).continuousOn
  have h2 : (2 : ℝ) ∈ Icc ((fun x : ℝ => x ^ 2) 0) ((fun x : ℝ => x ^ 2) 2) := by
    norm_num
  simpa using intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2) hcont h2
```

### Mathlib の証明の読み方

Mathlib の本体では，まず次のような少し強い形を証明しています．

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
`isClosed_le hf hg` によって，連続関数の大小関係で定まる集合が閉集合であることが分かります．
また任意の点 `x` では `le_total (f x) (g x)` により，少なくともどちらか一方の閉集合に入ります．
端点の仮定 `f a ≤ g a` と `g b ≤ f b` は，それぞれの閉集合が空でないことを与えます．

連結性はここで使われます．
`isPreconnected_closed_iff` は，preconnected な集合を 2 つの閉集合で覆い，
両方に点があるなら，2 つの閉集合の交わりにも点がある，という形の補題です．
その交点の点 `x` では

```lean4
f x ≤ g x,   g x ≤ f x
```

が同時に成り立つので，`le_antisymm` から `f x = g x` が出ます．

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
