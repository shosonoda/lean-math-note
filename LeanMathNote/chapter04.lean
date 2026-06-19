import Mathlib --#
set_option linter.missingDocs false --#

namespace Chapter04 --#

/-
# Chapter 04: Mathlib を用いた証明の書き方

この章では，Mathlib を使って証明を書くときの基本的な読み方・書き方を整理します．
Mathematics in Lean の後半では，構造体，型クラス階層，代数構造，線形代数，位相，微積分，測度論などが現れます．
線形代数や微積分の各論は次章以降で扱い，ここではそれらに共通する Mathlib の作法を見ます．

特に次の内容を扱います．

* `import Mathlib` と名前空間・スコープつき記法
* 型クラスと階層
* `Finset`，`Real`，`ENNReal`
* bundled structure，morphism，subobject，coercion
* Mathlib で仮定される公理
* Mathlib の命名規則

なお，`Finset`，`Real`，`ENNReal` は「クラス」ではなく型です．
ただし，それらの型には `LinearOrder`，`TopologicalSpace`，`CompleteLinearOrder` などの型クラスインスタンスが登録されており，そのインスタンスによって一般定理や tactic が使えるようになります．
Mathlib を読むときは，「対象そのものの型」と「その型に入っている構造」を分けて見ることが重要です．

参考:

* Mathematics in Lean: <https://leanprover-community.github.io/mathematics_in_lean/index.html>
* Mathlib naming conventions: <https://leanprover-community.github.io/contribute/naming.html>
* Theorem Proving in Lean 4, Axioms and Computation: <https://leanprover.github.io/theorem_proving_in_lean4/Axioms-and-Computation/#axioms-and-computation>
* Sets in Mathlib: <https://leanprover-community.github.io/theories/sets.html>
-/

/-
---
## `import Mathlib` と `open scoped`

このプロジェクトでは各章の冒頭で `import Mathlib` を使っています．
これは Mathlib 全体を読み込むため，講義資料では便利です．
実際の開発では，ビルド時間を抑えるために必要なファイルだけを import することもあります．

一部の記法は，スコープを開かないと使えません．
有限和 `∑` には `BigOperators`，拡張非負実数の `∞` には `ENNReal` のスコープを使います．
`open scoped` は名前空間の中の定義名を短くするというより，特定の記法やスコープ付き記法を有効にするために使います．
-/

open scoped BigOperators
open scoped ENNReal

/-
`#check` は，Mathlib の名前がどのような型をもつかを確認する基本コマンドです．
`#synth` は，指定した型クラスインスタンスを Lean が見つけられるかを確認します．
-/

#check Finset
#check Real
#check ENNReal
#check ℝ
#check (∞ : ENNReal)

#synth Field ℝ
#synth LinearOrder ℝ
#synth TopologicalSpace ℝ
#synth Add ENNReal
#synth CompleteLinearOrder ENNReal

/-
---
## 型クラスで一般化された定理を読む

Mathlib の定理は，特定の型だけではなく，型クラスで一般化された形で書かれることがよくあります．
たとえば `add_comm` は自然数専用の定理ではなく，足し算が可換な任意の型で使える定理です．
`#check add_comm` の結果を見ると，必要な型クラス仮定が明示されます．
-/

#check add_comm
#check add_zero
#check le_total

section GenericAlgebra

variable {α : Type*} [AddCommMonoid α]

example (a b : α) : a + b = b + a := by
  exact add_comm a b

example (a : α) : a + 0 = a := by
  exact add_zero a

end GenericAlgebra

/-
角括弧 `[AddCommMonoid α]` は，「`α` には加法可換モノイド構造がある」というインスタンスを要求します．
Lean はこの仮定を使って `+` や `0` の意味を決め，`add_comm` や `add_zero` を適用します．
実際には `add_comm` だけならより弱い `AddCommMagma` で十分ですが，ここでは `add_zero` も同じ section で使うため `AddCommMonoid` を仮定しています．
`Type*` は universe レベルを Lean に推論させる記法で，`Type u` の universe 変数を明示しない書き方です．
-/

section GenericOrder

variable {α : Type*} [LinearOrder α]

example (a b : α) : a ≤ b ∨ b ≤ a := by
  exact le_total a b

end GenericOrder

/-
このように，Mathlib の多くの定理は「型 `α` と，その型に入っている構造」を分けて書きます．
後半の章で現れる `Group`，`Ring`，`TopologicalSpace`，`Module` なども同じ発想です．
-/

#check Group
#check Ring
#check TopologicalSpace
#check Module

/-
---
## `Finset`: 有限集合

`Finset α` は，型 `α` の元からなる有限集合です．
リストとは違い，重複を持たない集合として扱います．
一方で，有限集合なので `card`，有限和 `∑`，有限積 `∏` などを使えます．
`Finset α` は `Set α` に有限性を付けたものというより，有限個の要素をデータとして持つ型です．
そのため，計算や有限和・有限積との相性がよい一方，一般の集合論的な部分集合は `Set α` で表します．

Mathlib では，有限な対象や集合的な対象を表す方法がいくつかあります．

* `List α`: 順序と重複を持つ有限列です．計算や再帰に向いています．
* `Multiset α`: 順序を無視し，重複は残す有限多重集合です．
* `Finset α`: 順序も重複も無視する有限集合です．
* `Set α`: `α → Prop` として実装される一般の集合です．有限とは限りません．
* `Fintype α`: 型 `α` のすべての元が有限個である，という型クラスです．
* `Subtype`: 条件を満たす元を新しい型として扱う方法です．

したがって，順序つきのデータとして扱いたいなら `List`，重複個数を気にするなら `Multiset`，有限集合として和や濃度を扱いたいなら `Finset`，無限集合も含めた通常の集合なら `Set` を使います．

多くの操作では，元の等号を判定できること，つまり `[DecidableEq α]` が必要になります．
自然数 `Nat` にはそのインスタンスがあるため，次の例はそのまま動きます．
たとえば，要素を挿入したときに既に含まれているかどうかを判定するには，要素同士の等号を決定できる必要があります．
-/

#check List
#check Multiset
#check Finset
#check Set
#check Fintype
#check Subtype

example : (([1, 2, 1] : List Nat) : Multiset Nat) = (([1, 1, 2] : List Nat) : Multiset Nat) := by
  decide

example : ({1, 1, 2} : Finset Nat).card = 2 := by
  native_decide

example : ({1, 2} : Finset Nat) = ({2, 1} : Finset Nat) := by
  native_decide

example : (3 : Nat) ∈ Finset.range 5 := by
  simp

example : (5 : Nat) ∉ Finset.range 5 := by
  simp

example : (Finset.range 5).card = 5 := by
  simp

/-
`Finset.range n` は `{0, 1, ..., n - 1}` です．
有限和は `∑ i ∈ s, f i` の形で書けます．
-/

example : (∑ i ∈ Finset.range 4, i) = 6 := by
  native_decide

/-
`native_decide` は，決定可能な命題を実行時に計算して証明します．
有限集合の小さな具体例では便利ですが，一般の数学的証明では `simp`，`rw`，補題を使って構造的に示すのが普通です．
-/

/-
`Fintype α` は「型 `α` 全体が有限である」という型クラスです．
たとえば `Fin 3` は 3 個の元を持つ型で，`Finset.univ` はその型の全要素からなる有限集合です．
`Finset α` は「有限個の `α` の要素を集めたデータ」であり，`Fintype α` は「型 `α` 自身が有限である」という構造です．
-/

example : Fintype.card (Fin 3) = 3 := by
  rfl

example : (Finset.univ : Finset (Fin 3)).card = 3 := by
  rfl

/-
`Finset` と `Set` は相互に関係しますが，同じものではありません．
`Finset` は有限性をデータとして持つため，和や積を直接定義できます．
`Set α` は単に `α → Prop` なので，有限とは限らず，有限和には追加の有限性情報が必要です．
-/

/-
---
## 型と集合の違い

Lean では，型と集合を区別します．
`Nat` や `Real` は型であって，何か大きな宇宙の中の集合として直接表されているわけではありません．
一方，`Set Nat` は `Nat → Prop` の略記で，自然数を対象とする述語としての集合です．
この区別は Mathlib を読むうえで非常に重要です．
たとえば「自然数全体」は型 `Nat` として扱い，「自然数の部分集合」は `Set Nat` として扱います．
-/

def smallSet : Set Nat :=
  {n | n < 3}

abbrev smallSubtype : Type :=
  {n : Nat // n < 3}

example : 2 ∈ smallSet := by
  norm_num [smallSet]

example : (⟨2, by norm_num⟩ : smallSubtype).1 = 2 := by
  rfl

/-
`smallSet` は `Nat` の部分集合です．
要素 `n : Nat` について `n ∈ smallSet` という命題を考えます．
一方，`smallSubtype` は新しい型です．
その要素は，自然数 `n` と証明 `n < 3` の組です．

型であって集合ではない典型例は `Nat`，`Fin 3`，`Real` です．
これらは要素を持つ分類としての型です．
必要に応じて，`Set Nat` や `Set ℝ` のように，ある型の上の集合を別に定義します．
-/

example (x : smallSubtype) : (x : Nat) ∈ smallSet := by
  exact x.property

/-
---
## `Real`: 実数

Mathlib の実数型は `Real` で，記法として `ℝ` が使えます．
`ℝ` には体，線形順序，位相空間，距離空間など多くの型クラスインスタンスが入っています．
そのため，代数・順序・位相の一般定理を実数に適用できます．
`ℝ` は `Real` の記法であり，別の型ではありません．
-/

#check Real
#check ℝ
#check Real.sqrt
#check Real.sqrt_sq_eq_abs

example : ((3 : Nat) : ℝ) + 2 = 5 := by
  norm_num

example (x : ℝ) : 0 ≤ |x| := by
  exact abs_nonneg x

example (x : ℝ) : Real.sqrt (x ^ 2) = |x| := by
  simpa using Real.sqrt_sq_eq_abs x

/-
`norm_num` は数値計算に強い tactic です．
実数上の具体的な数値等式・不等式を閉じるときによく使います．
ただし，ここでは実数の各論には深入りせず，`ℝ` が豊かな型クラス構造を持つ型であることを押さえます．
-/

/-
---
## `ENNReal`: 拡張非負実数

`ENNReal` は extended nonnegative real，つまり `$[0, \infty]$` に対応する型です．
記法として `ℝ≥0∞` も使われます．
測度論では，測度や非負関数の積分値が `∞` になりうるため，`ENNReal` がよく現れます．
`ENNReal` では引き算や実数への変換が通常の実数と同じようには振る舞わないため，専用の補題を使う必要があります．
-/

#check ENNReal
#check ℝ≥0∞
#check ENNReal.ofReal
#check ENNReal.toReal

example : (0 : ENNReal) ≤ ∞ := by
  simp

example : (∞ : ENNReal) + 1 = ∞ := by
  simp

example : (1 : ENNReal) + 2 = 3 := by
  norm_num

/-
`ENNReal` は実数 `ℝ` とは別の型です．
`ℝ` から `ENNReal` への変換や，`ENNReal` から実数へ戻す操作には専用の関数や補題があります．
型が違うものを同じものとして扱わず，どの型にいるのかを常に確認するのが重要です．
たとえば `ENNReal.ofReal` は負の実数を `0` に送るため，単なる型変換ではなく意味のある関数です．
-/

/-
---
## bundled structure，morphism，subobject

Mathlib では，数学的対象を構造体として束ねることがよくあります．
たとえば準同型は，単なる関数ではなく「関数本体」と「演算を保つ証明」を持つ構造体です．
これを bundled structure と呼ぶことがあります．
bundled にすると，写像そのものと構造保存の証明を 1 つの対象として渡せるため，定理の仮定や合成の記述が整理されます．
-/

#check MonoidHom
#check RingHom
#check MonoidHom.map_one
#check map_add

example : (RingHom.id ℤ) 3 = 3 := by
  rfl

example (f : ℤ →+* ℤ) (x y : ℤ) : f (x + y) = f x + f y := by
  exact map_add f x y

/-
`ℤ →+* ℤ` は，整数環から整数環への環準同型です．
`map_add` は，加法を保つことを表す典型的な補題名です．
Mathlib では，`map_zero`，`map_one`，`map_mul`，`map_add` のように，写像が構造を保つ定理が統一的な名前で用意されています．
準同型 `f : ℤ →+* ℤ` は関数のように `f x` と適用できますが，内部的には関数だけでなく保存性の証明も持っています．
-/

/-
部分構造も bundled な対象として扱われます．
たとえば線形代数では `Submodule R M`，代数では `Subgroup G` や `Subsemiring R`，位相では部分空間に関する構造が現れます．
各論は次章以降で扱いますが，ここでは名前だけ確認しておきます．
-/

#check Submodule
#check Subgroup
#check Subsemiring

/-
---
## coercion と subtype

Mathlib では，自然な埋め込みは coercion として登録されています．
たとえば自然数を実数として使うとき，`((3 : Nat) : ℝ)` のように型を変換します．
coercion は便利ですが，エラーメッセージを読むときには「Lean がどの型からどの型へ自動変換したのか」を意識する必要があります．
-/

example : ((3 : Nat) : ℝ) = 3 := by
  norm_num

/-
`Subtype` は，条件を満たす要素を集めた型です．
`{n : Nat // 0 < n}` は，正の自然数とその証明を組にした型です．
値を元の型に戻すときは coercion が働きます．
`x.property` は，`x` が subtype の条件を満たすことの証明です．
-/

example (x : {n : Nat // 0 < n}) : 0 < (x : Nat) := by
  exact x.property

example (x : {n : Nat // 0 < n}) : (x : Nat) ∈ {n : Nat | 0 < n} := by
  exact x.property

/-
集合や部分構造の外延性には `ext` を使うことが多いです．
次の例では，集合の等式を元ごとの同値性に変えています．
-/

example (A B : Set Nat) : A ∩ B = B ∩ A := by
  ext x
  simp [and_comm]

/-
---
## Mathlib でよく使う証明パターン

Mathlib を使う証明では，まず既存の補題を探し，`rw`，`simp`，`exact`，`apply`，`ext` などで組み合わせます．
型クラスによって定理が一般化されているため，具体的な型ではなく一般的な構造に対する定理を使うことが多くあります．
-/

example (A B : Set Nat) (x : Nat) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by
  exact Set.mem_inter_iff x A B

example (A B : Set Nat) (x : Nat) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  exact Set.mem_union x A B

example (a b c : Nat) : a + b + c = a + (b + c) := by
  rw [Nat.add_assoc]

example (a b : Nat) : a + b = b + a := by
  simpa using Nat.add_comm a b

/-
`simpa using ...` は，既存の補題の形とゴールが少し違うときに便利です．
補題とゴールの両方を `simp` で正規化して一致させます．
Mathlib の証明では，既存補題を `exact` でそのまま使うより，`simpa using` で少し形を整えて使う場面がよくあります．
-/

/-
---
## Lean と公理

Mathlib は Lean のカーネル上に構築されたライブラリです．
Mathlib 自体が勝手に新しい推論規則を追加するわけではなく，Lean の基礎にある仕組みと，明示的に import された定義・定理を使います．

Theorem Proving in Lean 4 の "Axioms and Computation" で説明されているように，Lean の標準ライブラリには実用上重要な追加原理として，命題外延性，商，選択が加えられています．
これは Mathlib 独自の公理というより，Lean で通常の数学を行うための標準的な基礎です．

ここでは，それらの背景を次のように理解しておきます．

* 命題外延性: 論理的に同値な命題を等しい命題として扱えるようにする．
* 商: 同値関係で割った対象を作れるようにする．
* 選択: 存在から証拠を選ぶ操作を可能にし，古典数学を扱いやすくする．

これらは数学の形式化を大きく便利にします．
一方で，選択に依存する定義は一般に計算内容を持たないため，`noncomputable` として扱われます．
そのため，証明と計算を区別して読むことが重要です．

等式そのものは Lean の基本的な同一性型であり，追加公理というより核となる型理論の一部です．
したがって，等式，命題外延性，選択，商型を同じ意味で「追加公理」と呼ぶのは正確ではありません．
等式は基本の型理論に含まれ，命題外延性・選択・商型は通常の数学を扱うために使われる追加的な原理や構成です．
-/

/-
### 等式

等式 `a = b` は Lean の基本的な同一性型です．
`Eq.refl` は反射律，`Eq.rec` は等しいものの置き換えを表す原理です．
-/

#check Eq.refl
#check Eq.rec

example (α : Type) (a b : α) (h : a = b) (P : α → Prop) (ha : P a) : P b := by
  exact h ▸ ha

/-
### 命題外延性

`propext` は，`P ↔ Q` から命題としての等式 `P = Q` を得る原理です．
これは証明支援系で命題を扱いやすくするために重要です．
-/

#check propext

example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  exact propext h

/-
### 選択公理と `Classical`

Mathlib では古典論理を使うことが多くあります．
`Classical.choice` は非空な型から要素を選ぶ原理で，存在命題から具体的な証拠を取り出す `Classical.choose` の基礎になっています．
このような定義は一般に計算できないので，`noncomputable` として宣言します．
`Classical.choice` の入力は `Nonempty α` であり，`∃ x, P x` から証拠を取り出すときは `Classical.choose` と `Classical.choose_spec` を使う，という使い分けを押さえておくとよいです．
-/

#check Classical.choice
#check Classical.em

noncomputable def choosePositiveNat (h : ∃ n : Nat, 0 < n) : Nat :=
  Classical.choose h

example (h : ∃ n : Nat, 0 < n) : 0 < choosePositiveNat h := by
  exact Classical.choose_spec h

/-
### 商型

商型は，同値関係で割った対象を作るための仕組みです．
整数，有理数，多くの代数的構成で，商の存在は不可欠です．
Lean では `Quot` とその基本原理が用意されています．
-/

#check Quot
#check Quot.sound
#check Quot.lift

/-
商型を使うと，「代表元を選ばずに」同値類上の対象を定義できます．
ただし，代表元によらないことの証明が必要になるため，直接扱うよりも Mathlib で既に整備された構造を使うことが多いです．
-/

/-
---
## Mathlib の命名規則

Mathlib の名前には強い規則性があります．
命名規則を知っていると，補題を推測したり，検索結果を読むのが楽になります．

基本方針は次の通りです．

* 定理名や証明項は `snake_case`: `add_comm`, `mul_assoc`, `not_le_of_gt`
* 型，命題，構造体，クラスは `UpperCamelCase`: `Finset`, `MonoidHom`, `LinearOrder`
* 通常のデータや関数は `lowerCamelCase`
* 名前空間はドットで表す: `Nat.succ_ne_zero`, `Set.mem_inter_iff`
* 写像が構造を保つ補題は `map_add`, `map_mul`, `map_zero` のような名前になりやすい

ただし，古い名前や歴史的事情による例外もあります．
命名規則は検索の手がかりであって，完全な規格ではありません．
-/

#check Nat.succ_ne_zero
#check Set.mem_inter_iff
#check Set.mem_union
#check add_comm
#check mul_assoc
#check map_add

/-
記号に対応する語もある程度決まっています．
たとえば，`∈` は `mem`，`∩` は `inter`，`∪` は `union`，`≤` は `le`，`<` は `lt`，`↔` は `iff` です．
したがって，集合の所属条件を探すときには `mem_inter` や `mem_union` のような名前を予想できます．

また，定理名では結論が先に来ることがよくあります．
たとえば `not_le_of_gt` は「`>` から `¬ ≤` が従う」と読みます．
この名前は，結論 `not_le` と仮定 `of_gt` に分けて読むと分かりやすくなります．
-/

#check not_le_of_gt
#check lt_of_le_of_ne

/-
命名規則は公式の Mathlib naming conventions に整理されています．
新しい補題名を探すときは，記号を英語名に直し，名前空間と結論の形から推測するのが有効です．
-/

/-
---
## まとめ

Mathlib を使う証明では，具体的な対象だけでなく，それが持つ型クラスインスタンスを意識することが重要です．
`Finset`，`ℝ`，`ENNReal` は型であり，それらに登録された構造によって一般定理が使えます．

また，Mathlib の証明は既存補題の組み合わせです．
`#check`，`#synth`，命名規則，`simp`，`rw`，`ext`，`norm_num` を使いながら，ゴールに合う補題を探して適用します．

基礎面では，等式，命題外延性，選択，商型といった仕組みが重要です．
これらを意識すると，Mathlib の定義がなぜ `noncomputable` になるのか，なぜ quotient や coercion が頻繁に出るのかを理解しやすくなります．
-/
/-
---
## 演習問題

この章の演習では，Mathlib の名前を調べながら既存補題を使う演習をします．
`#check`，`#synth`，`simp`，`rw`，`norm_num`，`ext` を積極的に使ってください．

1. `#synth` で，実数が順序体であることを確認してください．

```lean
#synth LinearOrderedField ℝ
```

2. `Finset.range` の membership を `simp` で証明してください．

```lean
example : (3 : Nat) ∈ Finset.range 5 := by
  sorry

example : (5 : Nat) ∉ Finset.range 5 := by
  sorry
```

3. `Set.ext` を使って集合の等式を証明してください．

```lean
example {α : Type} (s t : Set α) : s ∩ t = t ∩ s := by
  -- `ext x`, `constructor`, `intro h` で進める．
  sorry
```

4. `propext` を使って，同値な命題を等しい命題として扱ってください．

```lean
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  exact propext h
```

5. `Classical.choose` と `Classical.choose_spec` を使って，存在命題から証拠を取り出してください．

```lean
noncomputable def chosenNatExercise (h : ∃ n : Nat, n > 10) : Nat :=
  Classical.choose h

example (h : ∃ n : Nat, n > 10) : chosenNatExercise h > 10 := by
  -- `Classical.choose_spec h`
  sorry
```

6. `Real` と `ENNReal` の型クラスインスタンスを調べてください．

```lean
#check Real
#check ENNReal
#synth TopologicalSpace ℝ
#synth CompleteLinearOrder ENNReal
```

7. 命名規則を使って，次の補題名を予想し，`#check` で確認してください．

```lean
#check Set.mem_inter_iff
#check Set.mem_union
#check not_le_of_gt
#check lt_of_le_of_ne
```

8. `Finset` と `Set` の違いを説明したうえで，有限和を計算してください．

```lean
example : (∑ i ∈ Finset.range 4, i) = 6 := by
  -- `native_decide` または `norm_num` 系を試す．
  sorry
```
-/

end Chapter04 --#
