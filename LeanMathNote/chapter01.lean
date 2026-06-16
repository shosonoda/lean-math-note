import Mathlib --#
set_option linter.missingDocs false --#

/-
# Chapter 01: 命題論理と述語論理の形式証明

Lean では，命題は `Prop` という型の項として表されます．
そして，命題 `P : Prop` の証明は，型 `P` をもつ項として扱われます．
この見方は「命題を型，証明を項として見る」考え方で，Curry--Howard 対応（カリー・ハワード対応），あるいは propositions-as-types（命題＝型対応）と呼ばれます．
証明項 `h : P` を作ることと，命題 `P` を証明することは同じことであり，Lean の型検査器が証明の正しさを保証します．
つまり，Lean における形式証明では「正しい証明であること」を，最終的には「指定された型をもつ項が構成できていること」として確認します．

タクティックモードでは，Lean が現在の「ゴール」を表示し，ユーザは `intro`，`exact`，`constructor`，`cases` などのタクティックでゴールを変形していきます．
各タクティックは最終的に証明項を作るための補助であり，完成した証明は Lean の小さなカーネルによって再度型検査されます．
以下では，自然演繹でよく使う推論規則を 1 つずつ確認し，対応する Lean の書き方を見ます．

---
## 証明図の読み方

証明図では，横線の上に前提，横線の下に結論を書きます．
右側の $(\to I)$ や $(\land E)$ は，使っている推論規則の名前です．
たとえば
$$
\frac{\Gamma \vdash P \to Q \quad \Gamma \vdash P}{\Gamma \vdash Q}\;(\to E)
$$
は，「同じ仮定の集まり $\Gamma$ のもとで $P \to Q$ と $P$ が証明できるなら，$Q$ が証明できる」と読みます．

ここで $\Gamma$ は「現在使ってよい仮定や変数の集まり」です．
Lean のコードでは，通常 $\Gamma$ という記号は直接書きません．
かわりに，`example` や `theorem` の引数，`intro` で導入した仮定，`cases` で場合分けして得た仮定が，Lean のローカルコンテキストとして管理されます．
VS Code の Infoview では，ゴールの上に並ぶ変数や仮定が，証明図の $\Gamma$ に対応します．

たとえば
```lean
example (P : Prop) (hP : P) : P := by
  exact hP
```
では，Lean のローカルコンテキストにはおおよそ `P : Prop` と `hP : P` があります．
このうち `hP : P` は「$P$ の証明を仮定として使ってよい」という意味で，証明図の $P \in \Gamma$ に対応します．
述語論理では，`x : α` のような対象変数もコンテキストに入ります．
証明図では，命題の仮定と対象変数をまとめて $\Gamma$ と省略している，と考えるとよいです．

`intro hP` は，含意を示す途中で一時的に `hP : P` をコンテキストに追加する操作です．
証明図では，これは横線の上側に出てくる $\Gamma, P \vdash Q$ の $P$ に対応します．
証明が終わると，その仮定は「もし $P$ ならば」という含意の中に閉じ込められ，結論は $\Gamma \vdash P \to Q$ になります．
-/

/-
---
## 命題論理

命題論理では，個々の命題 `P Q R : Prop` を対象にして，論理結合子
`∧`，`∨`，`→`，`¬`，`↔`，`True`，`False` を扱います．

Lean では，これらの論理記号も型として実装されています．
たとえば `P → Q` は「`P` の証明を受け取って `Q` の証明を返す関数型」です．
`P ∧ Q` は `And P Q`，`P ∨ Q` は `Or P Q`，`P ↔ Q` は `Iff P Q` の記法です．
また，`¬ P` は定義上 `P → False` の略記です．

したがって，論理結合子の導入規則は「その型の項を作る方法」，除去規則は「その型の項から情報を取り出して使う方法」と読めます．
この視点を持つと，`constructor` が導入規則，`cases` や `.left`，`.right` が除去規則に対応する理由が見えやすくなります．
-/

/-
### 仮定規則

すでに仮定 `hP : P` があるなら，結論 `P` はその仮定そのもので証明できます．
Lean では，仮定名を `exact` で渡します．

証明図:
$$
\frac{P \in \Gamma}{\Gamma \vdash P}\;(\mathrm{assumption})
$$

具体例:
「$n$ は偶数である」と仮定しているなら，証明の途中でそのまま「$n$ は偶数である」と言ってよい，という規則です．
-/

example (P : Prop) (hP : P) : P := by
  exact hP

/-
### 含意導入 `→` introduction

`P → Q` を証明するには，いったん `P` を仮定して，そのもとで `Q` を証明します．
Lean では `intro hP` により，ゴール `P → Q` を「仮定 `hP : P` のもとで `Q` を示す」というゴールに変えます．

証明図:
$$
\frac{\Gamma, P \vdash Q}{\Gamma \vdash P \to Q}\;(\to I)
$$

具体例:
「$n$ が偶数なら $n^2$ も偶数である」を示すとき，まず「$n$ は偶数である」と仮定し，その仮定のもとで「$n^2$ は偶数である」を示します．
-/

example (P Q : Prop) (hQ : Q) : P → Q := by
  intro _hP
  exact hQ

/-
### 含意除去 `→` elimination

含意除去は modus ponens です．
`hPQ : P → Q` と `hP : P` があれば，`hPQ hP : Q` が得られます．

証明図:
$$
\frac{\Gamma \vdash P \to Q \quad \Gamma \vdash P}{\Gamma \vdash Q}\;(\to E)
$$

具体例:
「収束する数列は有界である」と「数列 $(a_n)$ は収束する」が分かっていれば，「$(a_n)$ は有界である」と結論できます．
-/

example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  exact hPQ hP

/-
### 連言導入 `∧` introduction

`P ∧ Q` を証明するには，`P` の証明と `Q` の証明を両方与えます．
Lean では `constructor` がゴールを `P` と `Q` の 2 つに分解します．

証明図:
$$
\frac{\Gamma \vdash P \quad \Gamma \vdash Q}{\Gamma \vdash P \land Q}\;(\land I)
$$

具体例:
「$x > 0$」と「$y > 0$」をそれぞれ証明できれば，「$x > 0$ かつ $y > 0$」を証明できます．
-/

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

/-
### 連言除去 `∧` elimination

`h : P ∧ Q` があるなら，左成分 `h.left : P` と右成分 `h.right : Q` を取り出せます．

証明図:
$$
\frac{\Gamma \vdash P \land Q}{\Gamma \vdash P}\;(\land E_1)
\qquad
\frac{\Gamma \vdash P \land Q}{\Gamma \vdash Q}\;(\land E_2)
$$

具体例:
「$x > 0$ かつ $y > 0$」が分かっていれば，左成分として「$x > 0$」を取り出せますし，右成分として「$y > 0$」も取り出せます．
-/

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

/-
### 選言導入 `∨` introduction

`P ∨ Q` を証明するには，左側の `P` を証明するか，右側の `Q` を証明すれば十分です．
Lean では左を選ぶとき `Or.inl`，右を選ぶとき `Or.inr` を使います．

証明図:
$$
\frac{\Gamma \vdash P}{\Gamma \vdash P \lor Q}\;(\lor I_1)
\qquad
\frac{\Gamma \vdash Q}{\Gamma \vdash P \lor Q}\;(\lor I_2)
$$

具体例:
「$n = 0$」が分かっていれば，「$n = 0$ または $n > 0$」を結論できます．
同様に，「$n > 0$」が分かっている場合も「$n = 0$ または $n > 0$」を結論できます．
-/

example (P Q : Prop) (hP : P) : P ∨ Q := by
  exact Or.inl hP

example (P Q : Prop) (hQ : Q) : P ∨ Q := by
  exact Or.inr hQ

/-
### 選言除去 `∨` elimination

`h : P ∨ Q` から `R` を示すには，`P` の場合に `R` が出ることと，`Q` の場合に `R` が出ることを両方示します．
Lean では `cases h with` により，左の場合と右の場合に場合分けします．

証明図:
$$
\frac{\Gamma \vdash P \lor Q \quad \Gamma, P \vdash R \quad \Gamma, Q \vdash R}
{\Gamma \vdash R}\;(\lor E)
$$

具体例:
自然数 $n$ について「$n = 0$ または $n > 0$」が分かっていて，どちらの場合にも「$n \ge 0$」が言えるなら，結論として「$n \ge 0$」が言えます．
-/

example (P Q R : Prop) (h : P ∨ Q) (hPR : P → R) (hQR : Q → R) : R := by
  cases h with
  | inl hP =>
      exact hPR hP
  | inr hQ =>
      exact hQR hQ

/-
### 真の導入 `True` introduction

`True` は常に証明できます．
Lean では `True.intro` が `True` の標準的な証明です．

証明図:
$$
\frac{}{\Gamma \vdash \top}\;(\top I)
$$

具体例:
どのような仮定のもとでも，論理的に常に正しい命題 `True` は証明できます．
数学の議論では，情報を持たない自明な結論を置く場合に対応します．
-/

example : True := by
  exact True.intro

/-
### 偽からの除去 `False` elimination

`False` の証明があるなら，任意の命題 `P` を証明できます．
これは ex falso quodlibet と呼ばれます．
Lean では `False.elim hFalse` を使います．

証明図:
$$
\frac{\Gamma \vdash \bot}{\Gamma \vdash P}\;(\bot E)
$$

具体例:
もし仮定から「$0 = 1$」のような矛盾が導けてしまったなら，その矛盾から任意の命題を導けます．
もちろん，通常の一貫した数学では矛盾そのものを導けないように注意します．
-/

example (P : Prop) (hFalse : False) : P := by
  exact False.elim hFalse

/-
### 否定導入 `¬` introduction

Lean では `¬ P` は `P → False` の略記です．
したがって `¬ P` を証明するには，`P` を仮定して矛盾 `False` を導きます．

証明図:
$$
\frac{\Gamma, P \vdash \bot}{\Gamma \vdash \neg P}\;(\neg I)
$$

具体例:
「$\sqrt{2}$ は有理数である」と仮定すると矛盾が出ることを示せば，「$\sqrt{2}$ は有理数ではない」と結論できます．
-/

example (P Q : Prop) (hPQ : P → Q) (hNotQ : ¬ Q) : ¬ P := by
  intro hP
  exact hNotQ (hPQ hP)

/-
### 否定除去 `¬` elimination

`hP : P` と `hNotP : ¬ P` が同時にあると，`False` が得られます．
さらに `False.elim` を使えば任意の結論を導けます．

証明図:
$$
\frac{\Gamma \vdash P \quad \Gamma \vdash \neg P}{\Gamma \vdash \bot}\;(\neg E)
$$

具体例:
同じ文脈で「$x > 0$」と「$x > 0$ ではない」が同時に得られたら，矛盾 `False` が得られます．
-/

example (P : Prop) (hP : P) (hNotP : ¬ P) : False := by
  exact hNotP hP

example (P Q : Prop) (hP : P) (hNotP : ¬ P) : Q := by
  exact False.elim (hNotP hP)

/-
### 同値導入 `↔` introduction

`P ↔ Q` を証明するには，`P → Q` と `Q → P` の両方向を証明します．
Lean では `constructor` が 2 つの方向にゴールを分解します．

証明図:
$$
\frac{\Gamma, P \vdash Q \quad \Gamma, Q \vdash P}{\Gamma \vdash P \leftrightarrow Q}
\;(\leftrightarrow I)
$$

具体例:
「$P \land Q$ と $Q \land P$ は同値である」を示すには，$P \land Q$ から $Q \land P$ を示す方向と，$Q \land P$ から $P \land Q$ を示す方向の両方を証明します．
-/

example (P Q : Prop) (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  constructor
  · intro hP
    exact hPQ hP
  · intro hQ
    exact hQP hQ

/-
### 同値除去 `↔` elimination

`h : P ↔ Q` があるなら，`h.mp : P → Q` と `h.mpr : Q → P` を取り出せます．
名前の `mp` は modus ponens，`mpr` はその逆向きを表します．

証明図:
$$
\frac{\Gamma \vdash P \leftrightarrow Q \quad \Gamma \vdash P}{\Gamma \vdash Q}
\;(\leftrightarrow E_1)
\qquad
\frac{\Gamma \vdash P \leftrightarrow Q \quad \Gamma \vdash Q}{\Gamma \vdash P}
\;(\leftrightarrow E_2)
$$

具体例:
「$x = 0$ と $x^2 = 0$ は同値である」が分かっているなら，$x = 0$ から $x^2 = 0$ を得られます．
逆向きに，$x^2 = 0$ から $x = 0$ を得ることもできます．
-/

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q := by
  exact h.mp hP

example (P Q : Prop) (h : P ↔ Q) (hQ : Q) : P := by
  exact h.mpr hQ

/-
### 古典論理: 排中律

Lean の基本的な推論規則は構成的に読めます．
構成的論理では，一般の命題 `P` について `P ∨ ¬ P` を無条件に証明することはできません．
そのため，排中律 `P ∨ ¬ P` や背理法を使うときは，古典論理を使っていることを意識します．
命題ごとの排中律は `Classical.em P` で得られます．
Mathlib では古典論理を使う定理や tactic がよく使われますが，ここでは構成的に証明できる規則と古典論理に依存する規則を分けて見ることが重要です．

証明図:
$$
\frac{}{\Gamma \vdash P \lor \neg P}\;(\mathrm{LEM})
$$

具体例:
古典論理では，任意の命題 $P$ について「$P$ が成り立つ，または $P$ は成り立たない」と言えます．
たとえば「ある方程式に解が存在する，または存在しない」という形の主張です．
-/

example (P : Prop) : P ∨ ¬ P := by
  exact Classical.em P

/-
### 古典論理: 背理法

古典論理では，`¬ P` を仮定すると矛盾が出ることから `P` を結論できます．
Lean のタクティック `by_contra hNotP` は，ゴール `P` を証明するために `hNotP : ¬ P` を仮定します．
その後のゴールは `False` になります．
これは二重否定除去 `¬¬ P → P` と同じ強さをもつため，一般には古典論理の原理です．

証明図:
$$
\frac{\Gamma, \neg P \vdash \bot}{\Gamma \vdash P}\;(\mathrm{RAA})
$$

具体例:
「素数は無限に存在する」を背理法で示すとき，「素数は有限個しか存在しない」と仮定し，その仮定から矛盾を導いて，もとの命題を結論します．
-/

example (P : Prop) (h : ¬ P → False) : P := by
  by_contra hNotP
  exact h hNotP

/-
---
## 述語論理

述語論理では，命題変数だけでなく，対象の型 `α : Type` と，その対象に依存する命題
`P : α → Prop` を扱います．
`P a` は「対象 `a : α` が性質 `P` を満たす」という命題です．

Lean の `∀ x : α, P x` は，依存関数型，つまり「各 `x : α` に対して `P x` の証明を返す関数型」として読めます．
そのため，全称命題の証明 `h : ∀ x : α, P x` は，関数のように具体的な項 `a : α` に適用して `h a : P a` を得ます．
一方，`∃ x : α, P x` は，証人 `x : α` とその証人が性質を満たす証明 `P x` の組として読めます．
-/

/-
### 全称導入 `∀` introduction

`∀ x : α, Q x` を証明するには，任意の `x : α` を 1 つ取って `Q x` を証明します．
Lean では `intro x` により，全称量化された変数を仮定として導入します．
ここで重要なのは，導入した `x` は特別な性質を仮定していない「任意の」対象だという点です．
自然演繹では，この条件を固有変数条件と呼びます．

証明図:
$$
\frac{\Gamma, x : \alpha \vdash P(x)}{\Gamma \vdash \forall x : \alpha, P(x)}\;(\forall I)
\qquad (x \notin \mathrm{FV}(\Gamma))
$$

具体例:
「任意の実数 $x$ について $x^2 \ge 0$」を示すには，特別な性質を仮定しない任意の実数 $x$ を 1 つ取り，その $x$ について $x^2 \ge 0$ を示します．
-/

example (α : Type) (P Q : α → Prop)
    (hPQ : ∀ x : α, P x → Q x) (hP : ∀ x : α, P x) :
    ∀ x : α, Q x := by
  intro x
  exact hPQ x (hP x)

/-
### 全称除去 `∀` elimination

`h : ∀ x : α, P x` があるなら，具体的な `a : α` に代入して `h a : P a` を得られます．
Lean では，全称命題の証明を関数のように適用します．
これは Curry--Howard 対応のもとで，全称量化が依存関数型として扱われていることの現れです．

証明図:
$$
\frac{\Gamma \vdash \forall x, P(x)}{\Gamma \vdash P(t)}\;(\forall E)
$$

具体例:
「任意の実数 $x$ について $x^2 \ge 0$」が分かっていれば，具体的な実数 $a$ に代入して「$a^2 \ge 0$」を得られます．
-/

example (α : Type) (P : α → Prop) (a : α) (h : ∀ x : α, P x) : P a := by
  exact h a

/-
### 存在導入 `∃` introduction

`∃ x : α, P x` を証明するには，具体的な証人 `a : α` と，その証人が性質を満たす証明 `ha : P a` を与えます．
Lean では `Exists.intro a ha` と書けます．

証明図:
$$
\frac{\Gamma \vdash P(t)}{\Gamma \vdash \exists x, P(x)}\;(\exists I)
$$

具体例:
「$2$ は偶数である」と分かっていれば，証人として $2$ を与えることで「偶数が存在する」と証明できます．
-/

example (α : Type) (P : α → Prop) (a : α) (ha : P a) : ∃ x : α, P x := by
  exact Exists.intro a ha

/-
### 存在除去 `∃` elimination

`hExists : ∃ x : α, P x` から結論を得るには，証人 `x` と証明 `hx : P x` を取り出し，そのもとで結論を示します．
Lean では `cases hExists with` で存在命題を分解できます．
取り出した証人の名前はその枝の中だけで使える局所的な名前です．
したがって，結論そのものはその名前に依存してはいけません．
これも自然演繹では固有変数条件として表されます．

証明図:
$$
\frac{\Gamma \vdash \exists x : \alpha, P(x) \quad \Gamma, y : \alpha, P(y) \vdash R}
{\Gamma \vdash R}\;(\exists E)
\qquad (y \notin \mathrm{FV}(\Gamma, R))
$$

具体例:
「正の実数が存在する」と分かっていて，さらに任意の正の実数 $x$ から $x^2 > 0$ が従うなら，存在する証人を 1 つ取り出して「平方が正である実数が存在する」と結論できます．
-/

example (α : Type) (P Q : α → Prop)
    (hExists : ∃ x : α, P x) (hPQ : ∀ x : α, P x → Q x) :
    ∃ x : α, Q x := by
  cases hExists with
  | intro x hx =>
      exact Exists.intro x (hPQ x hx)

/-
### 全称と連言の組み合わせ

量化子と命題論理の規則は組み合わせて使います．
たとえば，すべての `x` について `P x ∧ Q x` が成り立つなら，すべての `x` について `P x` が成り立ち，すべての `x` について `Q x` が成り立ちます．

この例の証明図:
$$
\frac{
  \frac{
    \frac{\Gamma, x : \alpha \vdash \forall z : \alpha, P(z) \land Q(z)}
          {\Gamma, x : \alpha \vdash P(x)}\;(\forall E;\land E_1)
  }{
    \Gamma \vdash \forall x : \alpha, P(x)
  }\;(\forall I)
  \quad
  \frac{
    \frac{\Gamma, y : \alpha \vdash \forall z : \alpha, P(z) \land Q(z)}
          {\Gamma, y : \alpha \vdash Q(y)}\;(\forall E;\land E_2)
  }{
    \Gamma \vdash \forall y : \alpha, Q(y)
  }\;(\forall I)
}{
  \Gamma \vdash (\forall x, P(x)) \land (\forall x, Q(x))
}\;(\land I)
$$

Lean のコードでは，`constructor` で連言の 2 つの成分を別々に証明します．
それぞれの枝で `intro x` により任意の `x` を導入し，`h x : P x ∧ Q x` から `.left` または `.right` で必要な成分を取り出します．

具体例:
集合 $A$ のすべての元が「有理数であり，かつ正である」と分かっているなら，「すべての元が有理数である」と「すべての元が正である」を別々に取り出せます．
-/

example (α : Type) (P Q : α → Prop) (h : ∀ x : α, P x ∧ Q x) :
    (∀ x : α, P x) ∧ (∀ x : α, Q x) := by
  constructor
  · intro x
    exact (h x).left
  · intro x
    exact (h x).right

/-
### 存在と選言の組み合わせ

存在命題を使う証明では，まず証人を取り出してから，命題論理の規則を適用することがよくあります．
次の例では，`∃ x, P x` と `∀ x, P x → Q x ∨ R x` から，`∃ x, Q x ∨ R x` を示します．

この例の証明図:
$$
\frac{
  \Gamma \vdash \exists x, P(x)
  \quad
  \frac{\Gamma, y : \alpha, P(y) \vdash Q(y) \lor R(y)}
        {\Gamma, y : \alpha, P(y) \vdash \exists x, Q(x) \lor R(x)}
        \;(\exists I)
}{
  \Gamma \vdash \exists x, Q(x) \lor R(x)
}\;(\exists E)
$$

存在除去で得た局所的な証人 `x` は，そのまま結論の存在命題の証人として再利用できます．
このとき外に出しているのは局所変数そのものではなく，`Exists.intro x ...` で包み直した存在命題の証明です．

具体例:
ある整数 $n$ が存在し，任意の整数は偶数または奇数であると分かっているなら，証人 $n$ を取り出して「偶数または奇数である整数が存在する」と結論できます．
-/

example (α : Type) (P Q R : α → Prop)
    (hExists : ∃ x : α, P x) (hPQR : ∀ x : α, P x → Q x ∨ R x) :
    ∃ x : α, Q x ∨ R x := by
  cases hExists with
  | intro x hx =>
      exact Exists.intro x (hPQR x hx)

/-
### 等号導入 `=` introduction

等号つきの述語論理では，任意の項は自分自身に等しいです．
Lean では反射律を `rfl` で証明します．
`rfl` は単に文字列として同じ式だけでなく，定義展開や計算によって同じ式になる等式も閉じられます．
このような同一性を定義的等しさと呼びます．

証明図:
$$
\frac{}{\Gamma \vdash t = t}\;(=I)
$$

具体例:
任意の数 $a$ について，$a = a$ は反射律により成り立ちます．
-/

example (α : Type) (a : α) : a = a := by
  rfl

/-
### 等号除去: 置換

`hEq : a = b` があり，`ha : P a` があるなら，等しいものは同じ性質を満たすので `P b` が得られます．
Lean では `hEq ▸ ha` により，`ha` の型に現れる `a` を `b` に置き換えます．
反対向きに置換したいときは，等式を逆向きに使います．
たとえば `← hEq` は `b` を `a` に戻す向きの等式として使えます．

証明図:
$$
\frac{\Gamma \vdash a = b \quad \Gamma \vdash P(a)}{\Gamma \vdash P(b)}\;(=E)
$$

具体例:
$a = b$ と $a > 0$ が分かっていれば，等しいものは同じ性質を持つので $b > 0$ と結論できます．
-/

example (α : Type) (P : α → Prop) (a b : α) (hEq : a = b) (ha : P a) : P b := by
  exact hEq ▸ ha

/-
### 等号除去: 書き換え

等式はゴールの書き換えにも使えます．
`rw [hEq]` は，ゴール中の左辺を右辺に書き換えます．
仮定を書き換える場合は `rw [hEq] at h` のように書きます．
反対向きに書き換える場合は `rw [← hEq]` を使います．
次の例では，ゴール `f a = f b` の左辺に現れる `a` を `b` に書き換えることで，`f b = f b` になり，反射律で閉じられます．

証明図:
$$
\frac{\Gamma \vdash a = b}{\Gamma \vdash f(a) = f(b)}\;(\mathrm{congruence})
$$

具体例:
$a = b$ が分かっていれば，同じ関数 $f$ を両辺に適用して $f(a) = f(b)$ と書き換えられます．
たとえば $a = b$ から $\sin a = \sin b$ が従います．
-/

example (α β : Type) (f : α → β) (a b : α) (hEq : a = b) : f a = f b := by
  rw [hEq]

/-
---
## まとめ

命題論理の基本規則は，Lean では `intro`，`exact`，`constructor`，`cases`，`False.elim` などに対応します．
述語論理では，`∀` を関数のように適用し，`∃` を証人とその証明の組として扱います．
以降の数学の形式化では，これらの規則を明示的に使うだけでなく，`rw`，`simp`，`apply` などのタクティックで同じ推論をより短く書くこともあります．
-/

/-
---
## 演習問題

この章の演習では，まず証明図や自然言語の証明を考えてから Lean の tactic に翻訳してください．
`constructor`，`cases`，`intro`，`exact`，`False.elim`，`rw` を意識して使います．

1. 連言の可換性を証明してください．

```lean
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  -- `intro h` のあと，`constructor` と `h.left`, `h.right` を使う．
  sorry
```

2. 選言の可換性を証明してください．

```lean
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  -- `cases` で場合分けする．
  sorry
```

3. modus ponens を Lean で書いてください．

```lean
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  -- 関数適用として読む．
  sorry
```

4. `False` から任意の命題が従うことを証明してください．

```lean
example (P : Prop) (h : False) : P := by
  -- `False.elim h`
  sorry
```

5. 全称命題を使って具体的な元に関する結論を得てください．

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∀ x : α, P x → Q x) (a : α) (ha : P a) : Q a := by
  -- `h a ha`
  sorry
```

6. 存在命題から証人を取り出し，同じ証人で別の存在命題を作ってください．

```lean
example (α : Type) (P Q : α → Prop)
    (h : ∃ x : α, P x) (hpq : ∀ x, P x → Q x) :
    ∃ x : α, Q x := by
  -- `cases h with | intro x hx => ...`
  sorry
```

7. 等式を使って命題を書き換えてください．

```lean
example (α : Type) (P : α → Prop) (a b : α)
    (hab : a = b) (ha : P a) : P b := by
  -- `hab ▸ ha`
  sorry
```

8. 証明図を自分で書いてから，次の Lean 証明を完成させてください．

```lean
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) : P → R := by
  -- `intro hP`
  sorry
```
-/
