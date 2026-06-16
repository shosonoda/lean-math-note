import Mathlib --#
set_option linter.missingDocs false --#

namespace Chapter03 --#

/-
# Chapter 03: tactic，calc，induction による証明

この章では，Lean で証明を書くための基本的な道具を整理します．
前章までに，命題，型，定義，構造体，帰納型などを見ました．
ここでは，それらを使って実際に証明を進める方法に焦点を当てます．

特に次の内容を扱います．

* tactic モードの読み方
* tactic モードでない証明
* `exact`，`assumption`，`rfl`，`show`，`change`，`dsimp`
* `rw`，`nth_rw`，`simp`，`simpa`
* `conv` モード
* `apply`，`intro`，`specialize`
* `have`，`suffices`
* `constructor`，`obtain`，`rintro`，`rcases`，`cases`，`left`，`right`
* `by_cases`，`by_contra`，`push Not`，`exfalso`，`contradiction`
* `calc` モード
* `congr`，`ext`，`funext`
* `induction`
* `decide`，`aesop`，`grind`
* `loogle` などの検索コマンド

`ring`，`nlinarith`，`linarith` などの代数・不等式向け tactic は，次章の Mathlib を使う証明で扱います．
-/

/-
---
## tactic モードの基本

`by` 以降に tactic を並べる書き方を tactic モードと呼びます．
Lean は現在のゴールを持っていて，各 tactic はそのゴールを変形したり閉じたりします．
VS Code の Infoview では，上側にローカルコンテキスト，下側に現在のゴールが表示されます．
tactic を 1 行実行するたびに，Lean は未解決のゴールを更新します．
すべてのゴールが閉じると，`by ...` 全体が証明項になります．

一番直接的な tactic は `exact` です．
ゴールと同じ型をもつ項や証明をすでに持っているとき，それを `exact` に渡します．
厳密には，ゴールの型と `exact` に渡す項の型が定義的に等しいときに使えます．
-/

example (P : Prop) (hP : P) : P := by
  exact hP

/-
`assumption` は，ローカルコンテキストの中からゴールと一致する仮定を探して使います．
-/

example (P Q : Prop) (hP : P) (_hQ : Q) : P := by
  assumption

/-
`rfl` は，両辺が定義を展開すれば同じになる等式を閉じます．
「計算すれば同じ」という等式によく使います．
-/

example : (fun n : Nat => n + 1) 2 = 3 := by
  rfl

/-
Lean の等式 `a = b` は `Eq a b` という型です．
`rfl` は `Eq.refl`，つまり反射律を使う tactic です．
反射律は本来 `a = a` を証明するものですが，Lean は両辺を計算・定義展開して同じ式になる場合にも `rfl` を受け入れます．
このように，計算や定義展開だけで同じと判定されることを「定義的に等しい」，英語で definitionally equal と言います．
-/

#check Eq
#check Eq.refl

example : Eq 3 3 := by
  rfl

example : (fun n : Nat => n + 1) 2 = 3 := by
  exact Eq.refl 3

/-
一方，数学的には正しい等式でも，定義的に等しくない場合は `rfl` では閉じません．
たとえば `a + b = b + a` は可換性の定理 `Nat.add_comm` を使って証明します．
このような「命題として証明された等式」は，`rw` などで書き換えに使います．
-/

example (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

def Positive (n : Nat) : Prop :=
  0 < n

/-
`show` は，現在のゴールを明示的に書く tactic です．
証明を読む人に「いま何を示しているか」を示すのに使えます．
`show` で書いた命題は，現在のゴールと定義的に等しくなければなりません．
-/

example (n : Nat) : n + 0 = n := by
  show n + 0 = n
  exact Nat.add_zero n

/-
`change` は，現在のゴールを定義的に等しい別の表示へ置き換える tactic です．
次の例では，`Positive 3` を定義通り `0 < 3` に変えています．
論理的に同値な任意の命題へ変えられるわけではありません．
-/

example : Positive 3 := by
  change 0 < 3
  decide

/-
`unfold` も定義を展開します．
特定の名前を明示的に展開したいときに使います．
-/

def double (n : Nat) : Nat :=
  n + n

example : double 4 = 8 := by
  unfold double
  rfl

/-
`dsimp` は definitional simplification の略で，定義を展開して計算で簡約できる部分を整理します．
MiL では，関数を値に適用した式や，定義の中に隠れている全称量化を見やすくする場面で使われます．
`simp` と違って，一般の補題による書き換えではなく，主に定義展開と計算による簡約を行います．
-/

def FnUb (f : Nat → Nat) (a : Nat) : Prop :=
  ∀ x, f x ≤ a

example (f : Nat → Nat) (a : Nat) (h : FnUb f a) : f 0 ≤ a := by
  dsimp [FnUb] at h
  exact h 0

/-
---
## tactic モードでない証明

Lean の証明は，必ず tactic モードで書く必要はありません．
証明も項なので，命題の型をもつ式を直接書けば証明になります．
このような書き方を term-style proof，あるいは証明項による証明と呼ぶことがあります．
短い証明では term-style proof の方が構造が見えやすく，長い証明では tactic モードの方が途中状態を確認しやすいことがあります．
-/

example (P : Prop) (hP : P) : P :=
  hP

/-
含意の証明は関数です．
したがって，`P → Q` の証明は `fun hP => ...` という関数として書けます．
-/

example (P Q : Prop) (hQ : Q) : P → Q :=
  fun _hP => hQ

/-
連言の証明は `And.intro` で直接作れます．
tactic モードの `constructor` は，内部的にはこのようなコンストラクタを使う証明に対応しています．
-/

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
  And.intro hP hQ

/-
名前つき定理でも，右辺に証明項を直接書けます．
短い証明では，この書き方の方が読みやすい場合があります．
-/

theorem term_add_zero (n : Nat) : n + 0 = n :=
  Nat.add_zero n

/-
`calc` も tactic ではなく，証明項を作る式です．
そのため，次のように `by` なしで定理の右辺に置けます．
-/

example (a b c : Nat) : (a + b) + c = b + (a + c) :=
  calc
    (a + b) + c = (b + a) + c := by
      rw [Nat.add_comm a b]
    _ = b + (a + c) := by
      rw [Nat.add_assoc]

/-
tactic モードは「ゴールを変形する手続き」として読みやすく，証明項は「証明そのものを式として組み立てる」書き方です．
実際の開発では，短い証明は証明項で書き，長い証明や探索的な証明は tactic モードで書く，という使い分けがよくあります．
-/

/-
---
## `intro` と `apply`

含意 `P → Q` や全称命題 `∀ x, P x` を示すときは，`intro` で仮定や変数を導入します．
ゴールが `P → Q` なら `intro hP` は `hP : P` をローカルコンテキストに追加し，ゴールを `Q` に変えます．
ゴールが `∀ x : α, P x` なら `intro x` は任意の `x : α` を導入し，ゴールを `P x` に変えます．
-/

example (P Q : Prop) (hQ : Q) : P → Q := by
  intro _hP
  exact hQ

example (P : Nat → Prop) (h : ∀ n : Nat, P n) : P 0 := by
  exact h 0

/-
`apply` は，現在のゴールを証明するために使えそうな定理や仮定を適用します．
ゴールが `R` で，`hQR : Q → R` があるとき，`apply hQR` により新しいゴールは `Q` になります．
より一般には，結論が現在のゴールと一致するような定理を後ろ向きに使い，その定理の前提を新しいゴールとして残します．
-/

example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  apply hQR
  apply hPQ
  exact hP

/-
全称命題を具体的な値に適用したいときは，関数適用のように書けます．
`specialize` は，全称命題の仮定を特定の値に特殊化して，仮定そのものを書き換える tactic です．
次の例では，`h : ∀ n, P n → Q n` が `specialize h 3` によって `h : P 3 → Q 3` に変わります．
-/

example (P Q : Nat → Prop) (h : ∀ n : Nat, P n → Q n) (hP : P 3) : Q 3 := by
  specialize h 3
  exact h hP

/-
---
## `rw`: 等式による書き換え

`rw [h]` は，等式 `h : a = b` を使って，ゴール中の `a` を `b` に書き換えます．
命題の中では，同値 `P ↔ Q` も書き換えに使えます．
`rw` は指定された補題を左から右へ使い，`rw [← h]` と書くと逆向きに使います．
-/

example (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]

/-
書き換えの向きを逆にしたいときは `←` を使います．
-/

example (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]

example (a b : Nat) : b + a = a + b := by
  rw [← Nat.add_comm a b]

/-
仮定の中を書き換えるときは `rw [h] at h2` のように `at` を使います．
-/

example (a b c : Nat) (h : a = b) (h2 : a + c = 10) : b + c = 10 := by
  rw [h] at h2
  exact h2

/-
`nth_rw` は，複数ある候補のうち，何番目だけを書き換えるかを指定します．
番号は 1 から数えます．
通常の `rw` が意図しない場所を書き換えてしまうとき，局所的な制御に使います．
-/

example (a b c : Nat) (h : a + b = c) : (a + b) + (a + b) = c + (a + b) := by
  nth_rw 1 [h]

/-
`congr` は，両辺に同じ関数が適用されている等式を，引数の等式に帰着します．
たとえば `f a = f b` を示す問題を `a = b` に変えることができます．
次の例では，残った `a = b` のゴールをローカルコンテキストの `h : a = b` が閉じています．
-/

example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by
  congr

/-
---
## `conv` モード

`conv` モードは，ゴール全体ではなく，式の特定の部分に入り込んで書き換えるためのモードです．
通常の `rw` はゴール全体から書き換え場所を探します．
一方，`conv` では「左辺に入る」「第 1 引数に入る」のように場所を指定してから書き換えます．
-/

example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  conv_lhs =>
    rw [Nat.add_comm a b]

/-
`conv_lhs` は等式の左辺に入る省略記法です．
より一般には `conv =>` の中で `lhs` や `rhs` を使って，左辺・右辺を選べます．
-/

example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  conv =>
    lhs
    arg 1
    rw [Nat.add_comm a b]

/-
上の例では，左辺 `(a + b) + c` に入り，さらに第 1 引数 `a + b` に入ってから，そこだけを交換しています．
`arg 1` は関数適用や演算の第 1 引数へ移動する指示です．
-/

example (a b c : Nat) : (a + b) + (c + 0) = (a + b) + c := by
  conv_lhs =>
    arg 2
    rw [Nat.add_zero]

/-
`conv` の中でも `simp` を使えます．
式の一部だけを簡約したいときに便利です．
-/

example (a b : Nat) : (fun x : Nat => x + b) a = a + b := by
  conv_lhs =>
    simp

/-
`conv` は強力ですが，構文が細かく，証明が読みにくくなることもあります．
まずは通常の `rw` や `simp` を試し，書き換える場所を厳密に指定したいときに `conv` を使うのがよいです．
-/

/-
---
## `simp` と `simpa`

`simp` は，定義展開，既知の単純化補題，仮定を使った書き換えを組み合わせて，ゴールを単純化します．
日常的に最もよく使う tactic の 1 つです．
`simp` は登録された `[simp]` 補題を，原則として式が単純になる向きに使います．
任意の定理を総当たりで使う tactic ではないので，使ってほしい定義や補題は `simp [name]` の形で明示します．
-/

example (n : Nat) : n + 0 = n := by
  simp

example (xs : List Nat) : xs ++ [] = xs := by
  simp

/-
追加で使いたい定義や補題を `simp [name]` の形で渡せます．
-/

def addZeroTwice (n : Nat) : Nat :=
  n + 0 + 0

example (n : Nat) : addZeroTwice n = n := by
  simp [addZeroTwice]

/-
仮定の中を単純化するときは `simp at h` と書けます．
`simp at *` と書くと，ローカルコンテキストとゴール全体を対象にできますが，証明が読みにくくなる場合もあります．
-/

example (n m : Nat) (h : n + 0 = m) : n = m := by
  simp at h
  exact h

/-
`simpa using h` は，`h` の型と現在のゴールを単純化して一致させます．
最後の一手として非常に便利です．
内部的には「`h` を使う前後で `simp` する」と考えると読みやすいです．
-/

example (n m : Nat) (h : n + 0 = m) : n = m := by
  simpa using h

/-
`simp_all` は，ゴールとローカルコンテキストの仮定をまとめて単純化します．
仮定が多いときに有効です．
-/

example (n m : Nat) (h : n = m) : n + 1 = m + 1 := by
  simp_all

/-
---
## `have` と `suffices`

`have` は証明の途中で補題を作ります．
長い証明では，途中結果に名前をつけると読みやすくなります．
`have h : Q := ...` と書くと，以降の証明で `h : Q` を仮定として使えます．
-/

example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  have hQ : Q := hPQ hP
  exact hQR hQ

/-
`suffices h : Q` は，「`Q` が示せれば現在のゴールが従う」という形で証明を組み替えます．
先に最終段階を宣言し，あとで十分条件を証明する書き方です．
証明の流れとしては，まず `Q` から元のゴールを導く部分を書き，その後で `Q` 自体を証明します．
-/

example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  suffices hQ : Q from hQR hQ
  exact hPQ hP

/-
---
## 論理の tactic

連言 `P ∧ Q` や同値 `P ↔ Q` を示すときは，`constructor` がゴールを左右に分けます．
`constructor` は現在のゴールの型のコンストラクタを使って，必要なフィールドや前提をサブゴールとして生成します．
-/

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

example (P Q : Prop) (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  constructor
  · intro hP
    exact hPQ hP
  · intro hQ
    exact hQP hQ

/-
連言や存在命題を分解するときは `obtain` が便利です．
`obtain ⟨hP, hQ⟩ := h` は，`h` をパターンに従って分解し，得られた成分に名前をつけます．
-/

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hP, hQ⟩ := h
  constructor
  · exact hQ
  · exact hP

example (P : Nat → Prop) (h : ∃ n : Nat, P n) : ∃ n : Nat, P n := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn⟩

/-
`rintro` は `intro` とパターン分解を同時に行います．
含意の仮定を導入しながら，連言や存在命題をすぐに分解したいときに便利です．
-/

example (P Q R : Prop) : (P ∧ Q → R) → P → Q → R := by
  rintro h hP hQ
  exact h ⟨hP, hQ⟩

/-
`rcases` は，仮定をパターンに従って分解します．
`cases` よりも複雑な入れ子の分解を短く書けます．
-/

example (P Q R : Prop) (h : (P ∧ Q) ∨ R) : Q ∨ R := by
  rcases h with ⟨_hP, hQ⟩ | hR
  · left
    exact hQ
  · right
    exact hR

/-
存在命題を作るには，証人とその証明を与えます．
`use` は証人を指定する tactic です．
`use 3` の後，Lean は残りのゴールとして「その証人が条件を満たすこと」を要求します．
ここでは残ったゴール `3 + 2 = 5` が計算で閉じられます．
-/

example : ∃ n : Nat, n + 2 = 5 := by
  use 3

/-
選言 `P ∨ Q` を示すには，`left` または `right` でどちらを示すかを選びます．
-/

example (P Q : Prop) (hP : P) : P ∨ Q := by
  left
  exact hP

example (P Q : Prop) (hQ : Q) : P ∨ Q := by
  right
  exact hQ

/-
選言や帰納型の値を分解するには `cases` を使います．
-/

example (P Q R : Prop) (h : P ∨ Q) (hPR : P → R) (hQR : Q → R) : R := by
  cases h with
  | inl hP =>
      exact hPR hP
  | inr hQ =>
      exact hQR hQ

example (n : Nat) : n = 0 ∨ ∃ k : Nat, n = k + 1 := by
  cases n with
  | zero =>
      left
      rfl
  | succ k =>
      right
      exact ⟨k, rfl⟩

/-
`by_cases h : P` は，命題 `P` が成り立つ場合と成り立たない場合に分けます．
一般の命題 `P : Prop` に対する場合分けは，古典論理の排中律に依存します．
`P` が計算で判定可能な命題なら，その判定手続きに基づく場合分けとしても読めます．
-/

example (P : Prop) : P ∨ ¬ P := by
  by_cases h : P
  · left
    exact h
  · right
    exact h

/-
`by_contra h` は背理法です．
ゴール `P` を示すかわりに `h : ¬ P` を仮定して矛盾を導きます．
これは一般には古典論理の原理です．
構成的に証明したい場面では，`¬ P` を仮定して `False` を示す「否定の証明」と区別して使います．
-/

example (P : Prop) (h : ¬¬ P) : P := by
  by_contra hP
  exact h hP

/-
否定が量化子や論理結合子の外側にあるときは，`push Not` で内側へ押し込めます．
たとえば `¬ ∀ n, P n` は，古典論理のもとで `∃ n, ¬ P n` に変形されます．
-/

example (P : Nat → Prop) (h : ¬ ∀ n, P n) : ∃ n, ¬ P n := by
  push Not at h
  exact h

/-
`exfalso` は，現在のゴールを `False` に変えます．
矛盾を導けば任意のゴールが閉じる，という規則を使うための tactic です．
`False.elim` を tactic モードで使いやすくしたものと考えるとよいです．
-/

example (P Q : Prop) (hP : P) (hNotP : ¬ P) : Q := by
  exfalso
  exact hNotP hP

/-
`contradiction` は，コンテキストにある矛盾を探してゴールを閉じます．
-/

example (P Q : Prop) (hP : P) (hNotP : ¬ P) : Q := by
  contradiction

/-
---
## `calc` モード

`calc` は，等式や不等式の連鎖を数学の計算のように書くための構文です．
各行の右側に，そのステップの根拠を書きます．
各ステップは，前の行の右辺と次の行の左辺をつなぐ証明になっている必要があります．
-/

example (a b c : Nat) : (a + b) + c = b + (a + c) :=
  calc
    (a + b) + c = (b + a) + c := by
      rw [Nat.add_comm a b]
    _ = b + (a + c) := by
      rw [Nat.add_assoc]

/-
`calc` は等式だけでなく，推移律を持つ関係にも使えます．
次の例では `≤` の推移律を `calc` が使っています．
-/

example (a b c : Nat) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  calc
    a ≤ b := h₁
    _ ≤ c := h₂

/-
tactic モードの中で `calc` を使うこともできます．
-/

example (a b c : Nat) : (a + b) + c = b + (a + c) := by
  exact
    calc
      (a + b) + c = (b + a) + c := by
        rw [Nat.add_comm a b]
      _ = b + (a + c) := by
        rw [Nat.add_assoc]

/-
---
## 集合と関数: `ext` と `funext`

集合の等式を示すときは，外延性を使います．
`ext x` は，集合の等式を「任意の `x` について，`x` が左辺に属することと右辺に属することが同値である」に変えます．
集合だけでなく，構造体や関数などにも外延性定理が登録されている場合があります．
-/

example (A B : Set Nat) : A ∩ B = B ∩ A := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2, hx.1⟩
  · intro hx
    exact ⟨hx.2, hx.1⟩

/-
集合の基本的な所属条件は `simp` で展開できます．
-/

example (A : Set Nat) : A ∩ Set.univ = A := by
  ext x
  simp

/-
関数の等式は，すべての入力で値が等しいことを示せば証明できます．
この原理を関数外延性と呼び，Lean では `funext` を使います．
-/

example (f g : Nat → Nat) (h : ∀ x : Nat, f x = g x) : f = g := by
  funext x
  exact h x

/-
`ext` は関数にも使える場合があります．
ただし，関数の等式では `funext` の方が意図が明確です．
-/

example (f g : Nat → Nat) (h : ∀ x : Nat, f x = g x) : f = g := by
  ext x
  exact h x

/-
---
## `induction`: 帰納法

自然数やリストのような帰納型について証明するときは，`induction` を使います．
自然数 `n : Nat` に対する帰納法では，`zero` の場合と `succ n` の場合を証明します．
`cases` が単なる場合分けであるのに対して，`induction` は再帰的なコンストラクタの枝で帰納法の仮定を生成します．
-/

theorem nat_add_assoc_by_induction (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero =>
      simp
  | succ a ih =>
      simp [Nat.succ_add, ih]

/-
帰納法の帰納ステップでは，`ih` が帰納法の仮定です．
上の例では，`ih : (a + b) + c = a + (b + c)` を使って，`Nat.succ a` の場合を示しています．
-/

theorem list_length_map_by_induction {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih]

/-
自分で定義した帰納型に対しても `cases` や `induction` を使えます．
次の `Even` は「偶数である」という命題を帰納的に定義したものです．
`Even n` は `n` が偶数であることを表す命題であり，その証明は `zero` と `add_two` から作られます．
-/

inductive Even : Nat → Prop where
  | zero : Even 0
  | add_two {n : Nat} : Even n → Even (n + 2)

example : Even 4 := by
  apply Even.add_two
  apply Even.add_two
  exact Even.zero

example (h : Even 1) : False := by
  cases h

/-
帰納的に定義された命題の証明 `h : Even n` に対しても `induction h` が使えます．
これは「その証明がどのコンストラクタで作られたか」に関する帰納法です．
`cases h` は不可能なコンストラクタの枝を自動的に消すため，`Even 1` からは矛盾が得られます．
-/

theorem even_plus_two_of_even {n : Nat} (h : Even n) : Even (n + 2) := by
  exact Even.add_two h

example (n : Nat) (h : Even n) : Even (n + 2) := by
  induction h with
  | zero =>
      exact Even.add_two Even.zero
  | add_two h ih =>
      exact Even.add_two ih

/-
---
## 汎用的な tactic

`decide` は，Lean が真偽を計算できる命題を決定して証明します．
有限な計算で判定できる命題に有効です．
対象の命題に対する `Decidable` インスタンスがあり，計算結果が真である場合にゴールを閉じます．
-/

example : 3 < 5 := by
  decide

example : (2 + 2 = 4) := by
  decide

/-
`aesop` は，論理的な規則や登録された補題を使って探索する自動証明 tactic です．
命題論理，単純な述語論理，コンストラクタによる証明に強いです．
探索に失敗した場合は，どの補題が足りないのかを人間が切り分ける必要があります．
-/

example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  aesop

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  aesop

/-
`grind` は，書き換え，前向き推論，後ろ向き推論，場合分けなどを組み合わせる汎用自動化 tactic です．
強力ですが，何をしたのかが見えにくくなることもあるので，講義資料では短い例に限定して使います．
自動化 tactic は証明を短くしますが，初学段階ではまず手動の tactic でゴールの変化を追えるようにしておくことが重要です．
-/

example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  grind

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  grind

/-
`simp`，`aesop`，`grind` は便利ですが，証明が通らないときに原因を理解しにくいことがあります．
最初は `intro`，`apply`，`constructor`，`cases`，`rw` などで証明構造を書けるようにしてから，自動化を使うのがよいです．
-/

/-
---
## 検索系: `#check`，`exact?`，`rw?`，`loogle`

使える補題を探すことは，Lean で数学を形式化するときの大きな作業です．

`#check` は，名前が分かっている定理の型を確認します．
定理名が分かっている場合は `#check`，形だけ分かっている場合は `#loogle` や `exact?`，`rw?` のような検索支援を使い分けます．
-/

#check Nat.add_comm
#check Nat.add_assoc
#check Set.ext

/-
`exact?`，`rw?`，`try?` は，現在のゴールを閉じる候補や書き換え候補を提案する tactic です．
出力は環境や Mathlib のバージョンによって変わることがあるため，この資料では実行例としてだけ示します．

```lean
example (n : Nat) : n + 0 = n := by
  exact?

example (a b : Nat) : a + b = b + a := by
  rw?

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  try?
```

`loogle` は，定理を検索するためのコマンドです．
これは tactic ではなくコマンドなので，証明の中ではなくトップレベルで使います．
また，環境によっては Loogle サーバへの接続が必要です．

```lean
#loogle "_ + 0 = _"
#loogle Nat.succ
#loogle "commutative"
```
-/

/-
---
## まとめ

tactic モードでは，現在のゴールとローカルコンテキストを見ながら，証明を小さなステップに分解します．
`rw` と `simp` は書き換え，`intro` と `apply` は含意や全称命題，`constructor` と `cases` は論理結合子や帰納型，`induction` は帰納法に対応します．

`calc` は，数学の計算に近い形で等式や不等式の連鎖を書くための構文です．
`aesop` や `grind` は強力な自動化ですが，まずは基本 tactic で証明の構造を理解することが重要です．
-/
/-
---
## 演習問題

この章の演習では，同じ命題を複数の書き方で証明することを重視します．
まず tactic mode で証明し，余裕があれば term mode や `calc` でも書き直してください．

1. `intro` と `exact` だけで証明してください．

```lean
example (P Q : Prop) (hQ : Q) : P → Q := by
  sorry
```

2. `constructor` と `cases` を使って，連言の順序を入れ替えてください．

```lean
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  sorry
```

3. `rw` を使って等式を書き換えてください．

```lean
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  sorry
```

4. `calc` モードで加法の結合律・可換律を使って証明してください．

```lean
example (a b c : Nat) : a + b + c = b + a + c := by
  calc
    a + b + c = b + a + c := by
      -- `ac_rfl` または `rw [Nat.add_comm a b]` などを試す．
      sorry
```

5. `induction` で自然数の加法単位元を証明してください．

```lean
example (n : Nat) : n + 0 = n := by
  induction n with
  | zero =>
      sorry
  | succ n ih =>
      sorry
```

6. `conv` を使って，ゴールの一部だけを書き換えてください．

```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  conv_lhs =>
    rw [Nat.add_comm a b]
  rfl
```

7. `simp` で証明できる命題を，まず手動で証明し，その後 `simp` で短くしてください．

```lean
example (n : Nat) : n + 0 = n := by
  -- まず `induction`，次に `simpa` で試す．
  sorry
```

8. `aesop` または `grind` で閉じる論理問題を作り，手動証明と比較してください．

```lean
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (hP : P) : R := by
  -- `aesop` または `grind`
  sorry
```
-/

end Chapter03 --#
