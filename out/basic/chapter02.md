# Chapter 02: Lean の基本構文・型・データ構造

この章では，Lean のファイルを読むために必要な基本語彙を整理します．
前章では命題論理・述語論理の証明規則を見ました．
ここでは，それらの証明を書くための「言語としての Lean」を見ます．

扱う内容は次の通りです．

* コマンドと式
* `def`，`fun`，`example`，`theorem`，`lemma`
* `variable`，`section`，引数に現れる `( )`，`{ }`，`[ ]`
* `notation`
* `Prop`，`Type`，`Sort` と universe
* 関数型・依存関数型
* `inductive` 型，`structure`，`class`
* Chapter 01 で使った論理記号の実体
* `namespace`，`open`
* `abbrev`
* 積，直和型（非交和），`Option`，`List` などのデータ構造
* `if`，`match`，`let`，`do` などの制御構文

Lean では「プログラム」と「証明」は同じ構文で書かれます．
自然数を返す関数も，命題の証明も，どちらも型をもつ項です．
したがって，Lean のファイルを読むときは，まず「いま見ているものは環境に名前を追加するコマンドなのか，それとも型をもつ式なのか」を区別すると見通しがよくなります．

もう 1 つ重要なのは，「型」と呼ばれているものをいくつかの観点に分けて見ることです．
`Prop` や `Type` は型が住む階層です．
`α → β` や `∀ x : α, P x` は関数型・依存関数型です．
`Nat`，`List α`，`Option α`，`P ∨ Q`，`∃ x, P x` は `inductive` 型です．
`α × β`，`P ∧ Q`，`Subtype` は `structure` として実装された積型です．
`LE α` や `Add α` は型クラスで，`≤` や `+` の意味を型ごとに与えます．

この章では，Chapter 01 で使った `And`，`Or`，`Eq`，`LE`，`LT`，`True`，`False`，`Not`，`Exists`，`∀` なども，
単なる論理記号ではなく，Lean の具体的な定義・構文・型クラスとして見直します．

```lean
namespace Chapter02
```

---
## コマンドと式

Lean ファイルはコマンドの列です．
`import`，`def`，`theorem`，`inductive`，`structure`，`class`，`instance` などはコマンドです．
一方，`3`，`3 + 4`，`fun n => n + 1`，`Nat`，`P → Q` などは式です．

式は Lean によって elaboration され，型が決まります．
elaboration とは，ユーザが書いた構文や notation を，型情報を補いながら Lean の内部で扱う型付きの式へ変換する処理です．
この処理を担当する部分を elaborator と呼びます．
elaborator の詳しい仕組みは Chapter 06 で扱うので，ここでは「省略された引数や型クラス引数を補い，notation を実際の定義へ結びつける役割を持つ」と理解しておけば十分です．
コマンドは式そのものではなく，名前つき定義を追加する，型を確認する，評価する，名前空間に入る，といった操作を環境に対して行います．

たとえば `def` コマンドは，名前つきの定義を環境に追加します．
`#check` は式の型を確認するためのコマンドで，`#eval` は計算できる式を評価するためのコマンドです．
`example` は，名前を残さずに小さな項や証明を型検査するための匿名の宣言です．

```lean
def typedNat : Nat := 3

def typedProposition : Prop := 2 + 2 = 4

#check typedNat
#check typedProposition
#check (fun n : Nat => n + 1)
#eval typedNat + 4
```

`typedNat : Nat := 3` は，「`typedNat` という名前を定義し，その型は `Nat`，値は `3` である」と読みます．
同様に，`typedProposition : Prop := 2 + 2 = 4` は，「`typedProposition` という名前をもつ命題を定義する」と読みます．
型注釈 `: Nat` は省略できることもありますが，講義資料では意図を明示するために書くことが多いです．

```lean
def inferredNat := 10

example : inferredNat = 10 := by
  rfl
```

この講義資料の演習では，未完成の項や証明を表すために `sorry` を使うことがあります．
`sorry` はその場のゴールを仮に閉じるための穴で，Lean はその宣言に warning を出します．
したがって，演習中に「ここをあとで埋める」という印として使うことはできますが，完成した定義や定理には残さないものです．
`sorry` と tactic モードの関係は Chapter 03 で改めて扱います．

---
## `def`

`def` は計算内容をもつ定義を作るコマンドです．
関数，値，命題の略記などを定義できます．
`def name : T := t` は，「`name` という名前に，型 `T` の項 `t` を結びつける」と読みます．

```lean
def addTwo (n : Nat) : Nat :=
  n + 2

example : addTwo 3 = 5 := by
  rfl

def IsPositiveNat (n : Nat) : Prop :=
  0 < n

example : IsPositiveNat 3 := by
  unfold IsPositiveNat
  decide
```

`def` で定義した名前は，必要に応じて展開されます．
`rfl` で証明できる等式は，定義を展開して両辺が同じ形になる等式です．
この「定義を展開して同じになる」という同一性を，定義的な等しさと呼びます．
`def` で関数を定義すると，その計算規則を `rfl` や `simp` が利用できることがあります．

```lean
example : addTwo 0 = 2 := by
  rfl
```

---
## `fun`

`fun x => t` は無名関数を作る式です．
数学の notation では（関数名を明記しない） $x \mapsto t$ に対応します．
`def` が名前つきの関数を環境に追加するコマンドであるのに対して，`fun` はその場で関数という項を作る式です．

Lean の多引数関数は基本的にカリー化されています．
たとえば `Nat → Nat → Nat` は，自然数を 1 つ受け取って，さらに `Nat → Nat` 型の関数を返す型として読めます．
`fun x y => t` は，おおよそ `fun x => fun y => t` の短い書き方です．

```lean
#check (fun n : Nat => n + 1)
#check (fun m n : Nat => m + n)
#check (fun (P Q : Prop) (hP : P) (_hQ : Q) => hP)

def addByFun : Nat → Nat → Nat :=
  fun m n => m + n

example : addByFun 2 5 = 7 := by
  rfl

def addConst (k : Nat) : Nat → Nat :=
  fun n => n + k

example : addConst 4 3 = 7 := by
  rfl
```

関数を引数に取る関数へ，その場で関数を渡すときにも `fun` がよく使われます．
これは後で tactic を読むときにも重要です．
たとえば含意 `P → Q` の証明は，`P` の証明を受け取って `Q` の証明を返す関数です．

```lean
def applyTwice (f : Nat → Nat) (n : Nat) : Nat :=
  f (f n)

example : applyTwice (fun n => n + 1) 10 = 12 := by
  rfl

def composeNat (f g : Nat → Nat) : Nat → Nat :=
  fun n => f (g n)

example : composeNat (fun n => n + 1) (fun n => 2 * n) 5 = 11 := by
  rfl

example (P Q : Prop) : P → Q → P :=
  fun hP _hQ => hP
```

`fun` は tactic ではなく式です．
したがって，`exact fun hP => ...` のように書けば，「関数を証明項として直接与える」ことにもなります．
この見方は Chapter 03 で tactic と証明項の対応を見るときに使います．

### 演習

`fun` を使って，次の関数と証明項を書いてください．

```lean4
def squareByFunExercise : Nat → Nat :=
  -- `n ↦ n * n`
  sorry

example : squareByFunExercise 5 = 25 := by
  sorry

def applyToThreeExercise (f : Nat → Nat) : Nat :=
  -- `f` を `3` に適用する．
  sorry

example : applyToThreeExercise (fun n => n + 4) = 7 := by
  sorry

example (P Q : Prop) : P → Q → Q :=
  -- `fun` で証明項を書く．
  sorry
```

---
## `example`，`theorem`，`lemma`

`example` は名前を残さない匿名の宣言です．
構文やタクティックの小さな実験に向いています．
証明の文脈では `example : P := ...` は「命題 `P` の証明をその場で与える」という意味です．
ただし Lean のコマンドとしての `example` は，命題に限らず任意の型の項を匿名で確認する用途にも使えます．

```lean
example (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n

example : Nat :=
  42
```

命題そのものも式です．
次の最初の例では，`2 + 2 = 4` という命題が `Prop` 型の式であることを示しています．
次の例では，その命題の証明を与えています．

```lean
example : Prop :=
  2 + 2 = 4

example : 2 + 2 = 4 := by
  rfl
```

`theorem` は名前つきの定理を宣言します．
後からその名前を使って参照できます．
`theorem` で定義される名前は，ある命題 `P : Prop` を型にもつ項，つまり `P` の証明項です．
`theorem` や `lemma` の型は命題でなければなりません．
データや計算内容を名前つきで定義したいときは `def` を使います．

```lean
theorem add_zero_named (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n

theorem two_plus_two_is_four : 2 + 2 = 4 := by
  rfl

theorem positive_three_named : 0 < 3 := by
  decide

example : 5 + 0 = 5 := by
  exact add_zero_named 5

example : 2 + 2 = 4 := by
  exact two_plus_two_is_four

example : 0 < 3 := by
  exact positive_three_named
```

実用上は，補助的な定理を「lemma」と呼ぶことがよくあります．
Core Lean では，補助的な定理も `theorem` で宣言できます．
Mathlib を import している環境では `lemma` というコマンドもよく使われますが，ここでは Core Lean に合わせて `theorem` で書きます．

```lean
theorem zero_add_named (n : Nat) : 0 + n = n := by
  exact Nat.zero_add n

example : 0 + 5 = 5 := by
  exact zero_add_named 5
```

`example`，`theorem`，`lemma` はいずれも，命題を証明するためのコマンドです．
ただし，`example` は上で見たように，匿名の型検査例にも使えます．
命題証明として使う場合の違いは，主に「名前を残すか」「数学的にどのような位置づけか」です．

`def` との関係も重要です．
Lean の内部では，定義も定理も「名前に型つきの項を結びつける」という点では似ています．
たとえば `def` で `Nat` 型の値を定義することも，`Prop` 型の証明を定義することもできます．
ただし，数学的な命題の証明には，意図が明確になるように `theorem` や `lemma` を使うのが普通です．

```lean
def proofByDef : 1 + 1 = 2 := by
  rfl

example : 1 + 1 = 2 := by
  exact proofByDef
```

---
## `variable` と `section`

`variable` コマンドは，以降の定義や定理で使う変数をまとめて宣言します．
これは前章の証明図に出てきた `Γ`，つまり「現在使ってよい変数や仮定の集まり」に対応します．

`section ... end` で囲むと，その中だけで有効な変数を宣言できます．
宣言された変数は，後続の定義で実際に使われたとき，その定義の引数として自動的に追加されます．
たとえば次の `pairFromVariables` は，内部的には `α`，`x`，`y` を引数にもつ定義として扱われます．

```lean
section VariableExamples

variable (α : Type)
variable (x y : α)

def pairFromVariables : α × α :=
  (x, y)

example : pairFromVariables Nat 2 5 = (2, 5) := by
  rfl

end VariableExamples
```

波括弧 `{α : Type}` で宣言した引数は，Lean が推論できる場合には省略できる暗黙引数になります．
丸括弧 `(α : Type)` は通常の明示的な引数，波括弧 `{α : Type}` は暗黙引数です．
次の `singletonList 3` では，要素 `3` の型から `α = Nat` が推論されます．

```lean
section ImplicitVariableExamples

variable {α : Type}

def singletonList (x : α) : List α :=
  [x]

example : singletonList 3 = [3] := by
  rfl

example : singletonList (-2 : Int) = [(-2 : Int)] := by
  rfl

end ImplicitVariableExamples
```

### 引数に現れる `( )`，`{ }`，`⦃ ⦄`，`[ ]`

Lean の定義や定理では，引数の括弧に意味があります．
Mathlib の定理を読むときに重要なので，ここで整理しておきます．

* `(x : α)`: 明示的な引数です．通常，関数や定理を使う側が値を与えます．
* `{α : Type}`: 暗黙引数です．Lean が周囲の式から推論できるなら，通常は書きません．
* `⦃x : α⦄`: strict implicit 引数です．暗黙引数の一種で，
  Lean が後続の明示的な引数などから推論できるときに補います．
* `[Add α]`: 型クラス引数です．Lean が登録済みの `instance` から自動的に探します．

たとえば `(h : P)` は「命題 `P` の証明 `h` を明示的な引数として受け取る」という意味です．
一方，`{α : Type}` は命題の仮定ではなく，推論される型パラメータです．
`⦃x : α⦄` も推論される引数ですが，通常の暗黙引数よりも，後ろに続く明示的な引数から値が決まる場面を意識した書き方です．
入力するときは `{{x : α}}` と書くこともできますが，pretty printer では `⦃x : α⦄` と表示されます．
`[Add α]` も通常の変数というより，「`α` には足し算がある」という構造を型クラス探索で要求している，と読みます．
型クラスについては，後の `class` と `instance` の節で改めて扱います．

```lean
def explicitId (α : Type) (x : α) : α :=
  x

def implicitId {α : Type} (x : α) : α :=
  x

def strictImplicitExample ⦃x : Nat⦄ (_h : x = x) : Nat :=
  x

def addWithClass {α : Type} [Add α] (x y : α) : α :=
  x + y

#check explicitId
#check implicitId
#check @implicitId
#check strictImplicitExample
#check @strictImplicitExample
#check addWithClass

example : explicitId Nat 3 = 3 := by
  rfl

example : implicitId 3 = 3 := by
  rfl

example : strictImplicitExample (show (3 : Nat) = 3 from rfl) = 3 := by
  rfl

example : strictImplicitExample (x := 3) rfl = 3 := by
  rfl

example : (∀ ⦃n : Nat⦄, n = n → n = n) := by
  intro n h
  exact h

example (h : ∀ ⦃n : Nat⦄, n = n → n = n) : (3 : Nat) = 3 := by
  exact h rfl

example : addWithClass 2 5 = 7 := by
  rfl
```

暗黙引数を明示したいときは，名前付き引数 `(α := Nat)` を使うことがあります．
また，`@implicitId` のように名前の前に `@` を付けると，通常は隠れている暗黙引数も含めた型を確認できます．
strict implicit 引数も，必要なら `(x := 3)` のように名前付き引数で明示できます．

```lean4
#check @implicitId
#check implicitId (α := Nat)
#check @strictImplicitExample
```

最初は「丸括弧は普通に渡す，引数」，「波括弧は Lean が推論する，引数」，
「二重波括弧は，後続の情報から推論される暗黙引数」，
「角括弧は型クラス探索で探す，構造」と覚えておけば十分です．

---
## `notation`

Lean では，標準的な定義だけでなく，数学に近い記号や専用の構文を定義できます．
たとえば `α → β` は関数型の notation，`P ∧ Q` は `And P Q` の notation，`x ∈ s` は membership の notation です．
このような notation は，elaboration の過程で既存の定義や関数を使う式へ結びつけられます．

小さな notation なら，`notation` や `infix` で定義できます．

```lean
notation "twice(" n ")" => n + n

example : twice(3) = 6 := by
  rfl

infixl:65 " +++ " => Nat.add

example : 2 +++ 3 = 5 := by
  rfl
```

`notation "twice(" n ")" => n + n` は，`twice(3)` という notation を `3 + 3` と読むようにする指定です．
`infixl:65 " +++ " => Nat.add` は，中置 notation `x +++ y` を `Nat.add x y` と読むようにする指定です．
`65` は優先順位，`infixl` の `l` は左結合を表します．

実際の Mathlib では，`ℝ`，`∑`，`∈`，`⊔`，`→+*` など，多くの notation が定義されています．
notation は読みやすさのための糖衣構文なので，分からない notation に出会ったら，まず `#check` で型を確認し，「これはどの定義の別表記か」を調べるのが有効です．
講義資料では notation を使いますが，必要に応じて元の定義名も併記します．

---
## `Type`，`Prop`，`Sort`

まず，型そのものがどの階層に住んでいるかを整理します．
この節で扱う `Type`，`Prop`，`Sort` は「型の構成方法」ではなく，「型がどの階層にあるか」を表す語です．

`Type` は通常のデータ型が住む階層です．
たとえば `Nat : Type`，`Int : Type`，`List Nat : Type` です．
また `Type` 自身にも型があり，`Type : Type 1` です．
`Type : Type` としてしまうと自己言及的な循環が起きるため，Lean では `Type 0 : Type 1`，`Type 1 : Type 2`，... という階層を使います．

`Prop` は命題が住む階層です．
`P : Prop` の項は，命題 `P` の証明です．
`Sort` は `Prop` と `Type u` をまとめて扱うためのより一般的な階層で，おおまかに `Sort 0` が `Prop`，`Sort (u + 1)` が `Type u` に対応します．

```lean
#check Prop
#check Type
#check Type 1
#check Sort 0
#check Sort 1

universe u v

def sampleNumber : Nat := 42

def sampleList : List Nat := [1, 2, 3]

example : sampleList.length = 3 := by
  rfl

def idSort (α : Sort u) (x : α) : α :=
  x

example : idSort Nat 7 = 7 := by
  rfl

example (P : Prop) (h : P) : idSort P h = h := by
  rfl

def idType (α : Type u) (x : α) : α :=
  x

example : idType Nat 5 = 5 := by
  rfl

example : idType (List Nat) [1, 2] = [1, 2] := by
  rfl
```

`idSort` は `Prop` と `Type` の両方に使えます．
一方，通常の数学的対象を引数に取る関数では `α : Type u` と書くことが多いです．
この章では universe 変数を明示していますが，Lean が自動的に universe を推論してくれる場面も多くあります．

### 演習

`#check` で次の式の型を確認してください．

```lean4
#check Nat
#check (3 : Nat)
#check List Nat
#check Option Nat
```

---
## 関数型と依存関数型

型 `α β : Type` から構成される型 `α → β` は関数型です．
たとえば `Nat → Nat` は，自然数を受け取って自然数を返す型です．
関数型の項は式 `fun x => t` のように書けます．これは無名関数を作る式で，数学の $x \mapsto t$ に対応します．

```lean
def simpleTypedFunction : Nat → Nat :=
  fun n => n + 1

example : simpleTypedFunction 4 = 5 := by
  rfl

example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q :=
  hPQ hP
```

より一般には，返り値の型が入力の値に依存することがあります．
これを依存関数型と呼びます．
Lean では `(x : α) → β x` と書けます．
特に**全称命題**は，結論が命題であるような依存関数型 `(x : α) → P x` です．

例として，入力 `n` に応じて長さ `n` のベクトルを返す関数を考えます．
Lean では，長さ `n` の `Nat` ベクトルを `Vector Nat n` と書けます．
したがって `(n : Nat) → Vector Nat n` は，`n` を受け取ると「長さ `n` の自然数ベクトル」を返す型です．
これは返り値の型そのものが入力 `n` に依存しているので，依存関数型の例になっています．

次の `zeroVec n` は，`0` を `n` 回並べたベクトルです．
表示するときは `toList` で通常のリストに戻して確認します．

```lean
def zeroVec (n : Nat) : Vector Nat n :=
  Vector.replicate n 0

#check Vector
#check Vector.replicate
#check zeroVec
#check (zeroVec 4)
#eval (zeroVec 4).toList

example : (zeroVec 4).toList = [0, 0, 0, 0] := by
  rfl

#check ((n : Nat) → Vector Nat n)
```

なお，通常の `List Nat` でも「`0` が並んだリスト」を作れますが，型は常に `List Nat` なので，長さ `n` は型には現れません．
`Vector Nat n` を使うと，長さ `n` であることが返り値の型に入ります．

次の `IsEvenNat n` は，「自然数 `n` が偶数である」という命題です．
これは真偽値 `Bool` を返す判定関数ではなく，証明すべき命題を返す述語です．

```lean
def IsEvenNat (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k

example : IsEvenNat 4 := by
  unfold IsEvenNat
  exact ⟨2, rfl⟩
```

ここで `⟨2, rfl⟩` は，「具体的な値」と「その値が条件を満たす証明」をまとめたデータです．
「証拠として `k = 2` を選び，`4 = 2 * 2` は `rfl` で示せる」という意味です．
山括弧 `⟨...⟩` は，型が要求している部品を順に与えて値や証明を作るための notation です．
より正確には constructor を使う省略記法ですが，constructor 一般の説明は `structure` と `inductive` 型の節で扱います．

次の全称命題
`∀ n : Nat, IsEvenNat (2 * n)` は，各自然数 `n` に対して命題 `IsEvenNat (2 * n)` の証明を返す依存関数型です．
この見方が，Lean で「全称命題の証明を関数のように適用する」理由です．

```lean
#check (∀ n : Nat, IsEvenNat (2 * n))

theorem twice_is_even (n : Nat) : IsEvenNat (2 * n) := by
  unfold IsEvenNat
  exact ⟨n, rfl⟩

example : IsEvenNat (2 * 7) := by
  exact twice_is_even 7
```

### 演習

自然数を 2 倍する関数を `def` で定義し，簡単な計算例を証明してください．

```lean4
def twiceExercise (n : Nat) : Nat :=
  -- ここを埋める．
  sorry

example : twiceExercise 4 = 8 := by
  -- 定義通りなら `rfl` で閉じる．
  sorry
```

---
## `structure`

`structure` は，複数の field をもつデータ型を定義するコマンドです．
数学では，点，群，位相空間，線形写像などを `structure` として表すことが多くあります．
`structure` は，名前つき field をもつ積型と考えると分かりやすいです．
実際，Lean の内部では `structure` は単一の constructor をもつ `inductive` 型として扱われ，そこに field や射影関数の情報が登録されています．
そのため `inductive` 型と同様に再帰的な定義も受け付けますが，再帰的な出現は strictly positive でなければなりません．
field 名に対して射影関数が自動で作られ，`p.x` のようなドット notation でアクセスできます．

```lean
structure PointStruct where
  x : Int
  y : Int
deriving Repr, DecidableEq
```

`deriving Repr` は，`PointStruct` の値を Lean が表示できるようにする指定です．
`#eval` で値を確認したいときなどに使われます．

`deriving DecidableEq` は，2 つの `PointStruct` が等しいかどうかを判定する手続きを自動生成する指定です．
たとえば，2 つの点の座標がどちらも等しいかを計算で判定できるようになります．

この定義では，`x` と `y` が field です．
field は，その型の値が持つ名前つきの成分です．
一方，constructor はその型の値を作るものです．
`structure` では通常 `PointStruct.mk` という constructor が作られ，`{ x := 1, y := 2 }` はそれを使って点を作る notation です．

```lean
#check PointStruct.mk

example : PointStruct.mk 1 2 = { x := 1, y := 2 } := by
  rfl

def originStruct : PointStruct :=
  { x := 0, y := 0 }

def PointStruct.swap (p : PointStruct) : PointStruct :=
  { x := p.y, y := p.x }

example : originStruct.x = 0 := by
  rfl

example : PointStruct.swap { x := 1, y := 2 } = { x := 2, y := 1 } := by
  rfl
```

`PointStruct.x` や `PointStruct.y` は，`structure` の中で宣言された field です．
一方，`PointStruct.swap` は field ではなく，あとから `PointStruct` という名前空間に置いた普通の関数です．
Lean では，名前空間にある関数や定理も，最初の明示的な引数の型からドット notation で呼べることがあります．
そのため，`PointStruct.swap p` は `p.swap` とも書けます．
このような関数は，プログラミング言語のメソッドのように見えますが，
Lean の用語としては「名前空間にある関数」または「定理」をドット notation で適用している，と考えるのが安全です．
field かどうかは，それが `structure` や `class` の中で宣言された成分かどうかで判断します．

```lean
#check PointStruct.x
#check PointStruct.swap

example (p : PointStruct) : PointStruct.swap p = p.swap := by
  rfl

def addPointStruct (p q : PointStruct) : PointStruct :=
  { x := p.x + q.x, y := p.y + q.y }

example : addPointStruct { x := 1, y := 2 } { x := 3, y := 4 } = { x := 4, y := 6 } := by
  rfl
```

標準ライブラリでは，データの積 `Prod` も `structure` です．
`α × β` は `Prod α β` の notation で，`p.1` と `p.2` は field を取り出す射影です．

```lean
#check Prod
#check Prod.mk
#check Prod.fst

def sampleProduct : Nat × Nat :=
  (3, 5)

example : sampleProduct.1 = 3 := by
  rfl

example : sampleProduct.2 = 5 := by
  rfl

def sampleTriple : Nat × Nat × Nat :=
  (3, 5, 8)

example : sampleTriple.1 = 3 := by
  rfl

example : sampleTriple.2.1 = 5 := by
  rfl

example : sampleTriple.2.2 = 8 := by
  rfl
```

命題の連言 `P ∧ Q` も `And P Q` という `structure` です．
`h : P ∧ Q` から `h.left` と `h.right` を取り出すことは，structure の field を取り出すことと同じ形です．

```lean title="lean4/src/lean/Init/Prelude.lean"
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
```

ここで `intro ::` は，この `structure` の constructor 名を `intro` にする指定です．
つまり，`hP : P` と `hQ : Q` から `And.intro hP hQ : P ∧ Q` を作れます．
一方，`left` と `right` は field であり，作られた証明から左右の証明を取り出すために使われます．

```lean
#check And
#check And.intro
#check And.left
#check Subtype

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
  And.intro hP hQ

example (P Q : Prop) (h : P ∧ Q) : P :=
  h.left
```

命題の同値 `P ↔ Q` も `Iff P Q` という `structure` です．
`h : P ↔ Q` からは，`h.mp : P → Q` と `h.mpr : Q → P` を取り出せます．
これは同値命題を，両方向の含意を field としてもつ structure として表しているということです．

```lean title="lean4/src/lean/Init/Core.lean"
structure Iff (a b : Prop) : Prop where
  intro ::
  mp : a → b
  mpr : b → a
```

```lean
#check Iff
#check Iff.intro
#check Iff.mp
#check Iff.mpr

example (P Q : Prop) (hPQ : P → Q) (hQP : Q → P) : P ↔ Q :=
  Iff.intro hPQ hQP

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q :=
  h.mp hP
```

### 演習

2 つの成分を持つ `structure` を定義し，field を取り出してください．
また，3 つの積 `α × β × γ` から各成分を取り出す式を書いてください．

```lean4
structure PointExercise where
  x : Nat
  y : Nat

def pExercise : PointExercise :=
  { x := 2, y := 5 }

example : pExercise.x = 2 := by
  sorry

example (α β γ : Type) (x : α × β × γ) : α :=
  sorry
```

---
## `inductive` 型

`inductive` は，constructor によって項を作る型を定義するコマンドです．

`Sum`，`Option`，`List`，`Or`，`Exists`，`Eq` は代表的な `inductive` 型です．
`Sum α β` は左の型 `α` の値または右の型 `β` の値を持つ型で，`α ⊕ β` と書けます．数学の非交和 $\alpha \sqcup \beta$ に対応します．
`Option α` は値がある場合とない場合を表します．
`List α` は有限列です．
`Or` は命題の選言を表し，`P ∨ Q` と書けます．
`Exists` は存在命題を表し，`∃ x, P x` と書けます．
`Eq` は等式命題を表し，`a = b` と書けます．

実際の定義は，おおよそ次のようになっています．
`Sum` と `Exists` は `Init/Core.lean` にあり，`α ⊕ β` は `Sum α β` の notation です．

```lean title="lean4/src/lean/Init/Core.lean"
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β

@[inherit_doc] infixr:30 " ⊕ " => Sum

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
```

`Eq`，`Option`，`List`，`Or` は `Init/Prelude.lean` にあります．

```lean title="lean4/src/lean/Init/Prelude.lean"
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

inductive Option (α : Type u) where
  | none : Option α
  | some (val : α) : Option α

export Option (none some)

inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
```

`inductive` 型を見るときは，次の 3 つを確認すると読みやすくなります．

* 型を作る部分: 何を入れると型ができるか．例: `List : Type u → Type u`
* constructor: その型の項をどう作るか．例: `List.nil`，`List.cons`
* 消去・場合分け: `match`，`cases`，`induction` でどう使えるか．

`inductive` は，型そのものが引数を取る形でも定義できます．
たとえば `Option α` や `List α` は，型 `α` を 1 つ受け取って新しい型を作ります．
この場合，`#check` で型名だけを見ると，値の型ではなく「型から型を作る関数」のように見えます．

```lean
inductive MyOption (α : Type) where
  | none : MyOption α
  | some (x : α) : MyOption α

#check MyOption
#check (MyOption : Type → Type)
#check MyOption Nat
#check MyOption.none
#check MyOption.some
```

上の `#check MyOption` は，おおよそ

```lean4
MyOption : Type → Type
```

という意味です．
Lean の表示では `MyOption (α : Type) : Type` のように，引数つきの形で表示されることもあります．
`#check (MyOption : Type → Type)` と型注釈を付けると，`Type → Type` と見えていることを明示できます．
これは `MyOption` だけではまだ具体的な値の型ではなく，
`Nat` や `String` などの型を受け取って `MyOption Nat`，`MyOption String` という型を作る，という意味です．
一方，`#check MyOption Nat` は

```lean4
MyOption Nat : Type
```

となります．
つまり `MyOption Nat` は，「自然数が入っているかもしれない値」の型です．

```lean
def myOptionNat : MyOption Nat :=
  MyOption.some 3

def myOptionString : MyOption String :=
  MyOption.none

def myOptionGetD {α : Type} (default : α) : MyOption α → α
  | MyOption.none => default
  | MyOption.some x => x

example : myOptionGetD 0 myOptionNat = 3 := by
  rfl

example : myOptionGetD "empty" myOptionString = "empty" := by
  rfl
```

このように，引数を取る `inductive` 型では，
まず `MyOption Nat` のように型引数を与えて具体的な型を作り，
その型の項を constructor で作ります．
`List α` や `Option α` も同じパターンです．

```lean
inductive Sign where
  | negative
  | zero
  | positive
deriving Repr, DecidableEq

def signNeg : Sign → Sign
  | Sign.negative => Sign.positive
  | Sign.zero => Sign.zero
  | Sign.positive => Sign.negative

example : signNeg Sign.positive = Sign.negative := by
  rfl

example : signNeg Sign.zero = Sign.zero := by
  rfl


def sumLeft : Nat ⊕ Int :=
  Sum.inl 10

def sumRight : Nat ⊕ Int :=
  Sum.inr (-10)

#check (Sum.inl 10)
#check (Sum.inr (-10))

def sumToInt (x : Nat ⊕ Int) : Int :=
  match x with
  | Sum.inl n => Int.ofNat n
  | Sum.inr z => z

example : sumToInt (Sum.inl 7) = (7 : Int) := by
  rfl

example : sumToInt (Sum.inr (-3)) = (-3 : Int) := by
  rfl

def safePred (n : Nat) : Option Nat :=
  match n with
  | 0 => none
  | m + 1 => some m

example : safePred 0 = none := by
  rfl

example : safePred 4 = some 3 := by
  rfl

def listExample : List Nat :=
  [1, 2, 3].map (fun n => n + 1)

example : listExample = [2, 3, 4] := by
  rfl

def headD {α : Type u} (default : α) : List α → α
  | [] => default
  | x :: _ => x

example : headD 0 [5, 6, 7] = 5 := by
  rfl

example : headD 0 ([] : List Nat) = 0 := by
  rfl
```

`inductive` 型は再帰的にも定義できます．
次の `Tree α` は，値をもつ葉と，左右の部分木をもつ節点からなる二分木です．

```lean
inductive Tree (α : Type u) where
  | leaf (value : α)
  | node (left right : Tree α)

def Tree.size {α : Type u} : Tree α → Nat
  | Tree.leaf _ => 1
  | Tree.node left right => Tree.size left + Tree.size right

example : Tree.size (Tree.node (Tree.leaf 1) (Tree.leaf 2)) = 2 := by
  rfl
```

命題の選言 `P ∨ Q` は `Or P Q`，存在命題 `∃ x, P x` は `Exists (fun x => P x)` という `inductive` 型です．
Chapter 01 で `P ∨ Q` の証明に `left` や `right` を使ったのは，内部的には `Or.inl` や `Or.inr` で項を作っているからです．
仮定 `h : P ∨ Q` に `cases h` を使うと 2 つのゴールに分かれるのは，`Or` の constructor が 2 つあるからです．

```lean
#check Or
#check Exists
#check Eq

example (P Q : Prop) (hP : P) : P ∨ Q :=
  Or.inl hP

example (P Q R : Prop) (h : P ∨ Q) (hPR : P → R) (hQR : Q → R) : R :=
  Or.elim h hPR hQR

example (n : Nat) : n = n :=
  Eq.refl n
```

### 演習

また，`Or` と `Exists` を notation を使わずに作ってみてください．

```lean4
example (P Q : Prop) (hP : P) : Or P Q := by
  sorry

example : Exists (fun n : Nat => n = 2) := by
  sorry
```

---
## 型クラス `class` と `instance`

`class` は，型クラスを定義するコマンドです．
型クラスは，「この型にはこの構造や操作がある」という情報を Lean に登録し，必要な場所で自動的に探すための仕組みです．
`class` は構文上は `structure` に近く，field をもつデータとして定義されます．
内部的には，通常の `class ... where` は `structure` と同様に `inductive` 型として扱われます．
ただし `inductive` が「constructor で項を作る型」を定義するコマンドであるのに対し，`class` はその型を型クラス探索の対象として登録し，`[Add α]` のような引数を Lean が自動で探せるようにする点が本質的に異なります．
`instance` は，特定の型に対してその field を埋めた値を登録するコマンドです．

標準ライブラリの `LE`，`LT`，`Add` も型クラスです．

```lean title="lean4/src/lean/Init/Prelude.lean"
class LE (α : Type u) where
  le : α → α → Prop

class LT (α : Type u) where
  lt : α → α → Prop

class Add (α : Type u) where
  add : α → α → α
```

`x ≤ y` は `LE.le x y` の notation ですが，どの `LE.le` を使うかは `x` と `y` の型から決まります．
`+` も同様に `[Add α]` から `Add.add` を取り出して使います．
たとえば `LE.le (2 : Nat) 3` が書けるのは，`Nat` に対する `LE Nat` の instance があらかじめ登録されており，Lean がそれを型クラス探索で見つけるためです．

```lean
#check LE
#check LE.le
#check LT
#check LT.lt
#check Add
#check Add.add

example : LE.le (2 : Nat) 3 := by
  decide

example : (2 : Nat) ≤ 3 := by
  decide

example : Add.add (2 : Nat) 5 = 7 := by
  rfl

example : (2 : Nat) + 5 = 7 := by
  rfl
```

自分で定義した型にも，既存の数学的な型クラスの instance を登録できます．
次の `Vec2` は整数成分の平面ベクトルです．
`Vec2` 自体は具体的なデータ型なので `structure` として定義し，`class` にする必要はありません．
`class` にするのは，`Add` のように「ある型に備わる操作や構造」を型クラス探索で扱いたい場合です．
`instance : Add Vec2` を登録すると，`u + v` という notation が `Vec2` に対して使えるようになります．

```lean
structure Vec2 where
  x : Int
  y : Int
deriving Repr, DecidableEq

instance : Add Vec2 where
  add u v := { x := u.x + v.x, y := u.y + v.y }

def vecA : Vec2 :=
  { x := 1, y := 2 }

def vecB : Vec2 :=
  { x := 3, y := 4 }

example : vecA + vecB = { x := 4, y := 6 } := by
  rfl

example : Add.add vecA vecB = { x := 4, y := 6 } := by
  rfl
```

### 演習

型クラスを要求する関数の例として，加法を使う関数を定義してください．
また，`≤` と `<` が型クラスの field であることを `#check` で確認してください．

```lean4
def addThreeExercise {α : Type} [Add α] (a b c : α) : α :=
  -- `a + b + c`
  sorry

#check LE.le
#check LT.lt
```

---
## 論理記号の対応まとめ

Chapter 01 で使った論理記号は，ここまで見た依存関数型，`structure`，`inductive` 型，`class` の具体例として理解できます．
一覧にすると次のようになります．

| notation | 展開後の形 | 実装の種類 | 項を作る典型 | 情報を使う典型 |
| --- | --- | --- | --- | --- |
| `P → Q` | 非依存関数型 | 関数型 | `fun hP => ...` | `hPQ hP` |
| `∀ x : α, P x` | 依存関数型 | 依存関数型 | `fun x => ...` | `h x` |
| `P ∧ Q` | `And P Q` | `structure` | `And.intro hP hQ`，`⟨hP, hQ⟩` | `h.left`，`h.right` |
| `P ∨ Q` | `Or P Q` | `inductive` 型 | `Or.inl hP`，`Or.inr hQ` | `cases h`，`Or.elim h ... ...` |
| `∃ x : α, P x` | `Exists (fun x => P x)` | `inductive` 型 | `Exists.intro w hw`，`⟨w, hw⟩` | witness と証明に分解 |
| `a = b` | `Eq a b` | `inductive` 型 | `Eq.refl a`，`rfl` | `rw`，`subst` |
| `P ↔ Q` | `Iff P Q` | `structure` | `Iff.intro hPQ hQP`，`⟨hPQ, hQP⟩` | `h.mp`，`h.mpr` |
| `True` | `True` | `inductive` 型 | `True.intro` | ほぼ情報なし |
| `False` | `False` | constructor なしの `inductive` 型 | 通常は作れない | `False.elim h` |
| `¬ P` | `Not P`，すなわち `P → False` | `def` | `fun hP => ...` | `hNot hP : False` |
| `x ≤ y` | `LE.le x y` | `class LE` の field | 型ごとの定理や計算 | 型ごとの定理や計算 |
| `x < y` | `LT.lt x y` | `class LT` の field | 型ごとの定理や計算 | 型ごとの定理や計算 |

`∀` だけは，`And` や `Or` のような通常の名前つき `inductive` 型ではありません．
Lean の構文として依存関数型へ elaboration されます．

```lean
section LogicConnectivesAsTypes

variable (P Q R : Prop)

#check (P → Q)
#check (∀ n : Nat, IsEvenNat n)
#check (P ∧ Q)
#check (And P Q)
#check (P ∨ Q)
#check (Or P Q)
#check (∃ n : Nat, IsEvenNat n)
#check (P ↔ Q)
#check (Iff P Q)
#check ((2 : Nat) = 2)
#check ((2 : Nat) ≤ 3)
#check ((2 : Nat) < 3)

example (hP : P) (hQ : Q) : P ∧ Q :=
  And.intro hP hQ

example (h : P ∧ Q) : P :=
  h.left

example (hPQ : P → Q) (hQP : Q → P) : P ↔ Q :=
  Iff.intro hPQ hQP

example (h : P ↔ Q) (hP : P) : Q :=
  h.mp hP

example : True :=
  True.intro

example (h : False) : P :=
  False.elim h

example (hP : P) : ¬ ¬ P :=
  fun hNotP => hNotP hP

end LogicConnectivesAsTypes
```

---
## `namespace` と `open`

`namespace` は，名前を整理するためのコマンドです．
大きなプロジェクトでは，同じような名前の定義がたくさん出てきます．
名前空間を使うと，`Geometry.Point` のように，どの分野・モジュールの名前かを明示できます．

```lean
namespace Geometry

structure Point where
  x : Int
  y : Int
deriving Repr, DecidableEq

def origin : Point :=
  { x := 0, y := 0 }

def reflectX (p : Point) : Point :=
  { x := p.x, y := -p.y }

example : reflectX origin = origin := by
  rfl

end Geometry
```

名前空間の外から参照するときは，完全な名前 `Geometry.Point` や `Geometry.origin` を使います．
このファイル全体は `namespace Chapter02` の中にあるので，厳密な完全名は `Chapter02.Geometry.Point` です．
ただし，同じ `Chapter02` 名前空間の中では `Geometry.Point` と書けます．

```lean
example : Geometry.Point :=
  Geometry.origin

example : Geometry.reflectX Geometry.origin = Geometry.origin := by
  rfl
```

`open` は，名前空間の中の名前を短く使えるようにするコマンドです．
`open Geometry` と書くと，そのスコープ内では `Geometry.Point` を `Point`，`Geometry.origin` を `origin` と書けます．
ただし，読み手にとって由来が分かりにくくなることもあるので，必要な範囲に限定して使うのがよいです．

```lean
section OpenExamples

open Geometry

def reflectedOrigin : Point :=
  reflectX origin

example : reflectedOrigin = origin := by
  rfl

end OpenExamples
```

`namespace ... end` は新しい名前空間に入る構文で，そこで定義した名前はその名前空間に属します．
一方，`open` は既存の名前空間を開いて，名前を短く参照するための構文です．
つまり，`namespace` は名前を作る場所を決め，`open` は名前を読むときの省略を許す，と考えるとよいです．

### 演習

`namespace` を使って，同じ名前の定義が衝突しないことを確認してください．

```lean4
namespace AExercise
def value : Nat := 10
end AExercise

namespace BExercise
def value : Nat := 20
end BExercise

#check AExercise.value
#check BExercise.value
```

---
## `abbrev`

`abbrev` は略記を作るコマンドです．
`def` と似ていますが，「新しい概念を作る」というより「長い型や式に短い名前をつける」という意図を表します．
Lean は `abbrev` を展開しやすい略記として扱うので，型の同一視や型推論で邪魔になりにくいです．
一方で，数学的に意味のある新しい概念や，後で定理を付けたい対象には `def` を使うことが多いです．

```lean
abbrev NatPair := Nat × Nat

def sumNatPair (p : NatPair) : Nat :=
  p.1 + p.2

example : sumNatPair (2, 3) = 5 := by
  rfl
```

`NatPair` は `Nat × Nat` の略記なので，Lean は両者をほとんど同じものとして扱います．
このため，`Nat × Nat` 型の値をそのまま `NatPair` として使えます．

```lean
example (p : Nat × Nat) : NatPair := p
```

---
## 制御構文

Lean の制御構文は，通常のプログラミング言語の構文に似ています．
ただし Lean では，これらもすべて型をもつ式です．

### `if ... then ... else ...`

`if` は条件分岐です．
条件には，`Bool` または Lean が真偽を判定できる命題が入ります．
`n < 10` は命題ですが，自然数の大小比較には判定手続きがあるため `if` の条件として使えます．
一般の命題 `P : Prop` を条件にするには，Lean が `[Decidable P]` を見つけられる必要があります．

```lean
def minWithTen (n : Nat) : Nat :=
  if n < 10 then n else 10

example : minWithTen 3 = 3 := by
  rfl

example : minWithTen 20 = 10 := by
  rfl
```

### `match`

`match` は `inductive` 型やデータ構造を場合分けする式です．
`Option`，`List`，自分で定義した `inductive` などを分解できます．
各分岐は同じ型の式を返す必要があります．
証明で使う `cases` はゴールを場合分けする tactic ですが，`match` は式の中で場合分けして値を作る構文です．

```lean
def optionToNat : Option Nat → Nat
  | none => 0
  | some n => n

example : optionToNat none = 0 := by
  rfl

example : optionToNat (some 8) = 8 := by
  rfl

def listLength : List Nat → Nat
  | [] => 0
  | _ :: xs => 1 + listLength xs

example : listLength [10, 20, 30] = 3 := by
  rfl
```

### `let`

`let` は局所的な名前をつける構文です．
長い式を読みやすくするために使います．
`let` で導入した名前は，その式の残りの部分だけで使えます．
定義を環境に追加する `def` とは異なり，`let` は局所的な束縛です．

```lean
def squareSum (x y : Nat) : Nat :=
  let x2 := x * x
  let y2 := y * y
  x2 + y2

example : squareSum 3 4 = 25 := by
  rfl
```

### `do`

`do` notation は，モナド的な計算を順番に書くための構文です．
最初は，失敗するかもしれない計算を `Option` でつなぐ例として見るとよいです．
`do` ブロックの各行も式を組み立てるための notation であり，最終的には `bind` や `pure` を使う式に展開されます．

```lean
def addOptions (x y : Option Nat) : Option Nat := do
  let a ← x
  let b ← y
  pure (a + b)

example : addOptions (some 2) (some 5) = some 7 := by
  rfl

example : addOptions none (some 5) = none := by
  rfl
```

`let a ← x` は，`x` が `some a` なら中身を取り出して続行し，`none` なら全体を `none` にする，という動きをします．
同様に `let b ← y` で `y` が `none` なら，以降の `pure (a + b)` は実行されず，結果は `none` になります．
証明では `do` notation を頻繁に使うわけではありませんが，Lean でプログラムを書くときには重要です．

---
## まとめ

Lean の基本は「すべての式には型がある」という考え方です．
`Prop` は命題，`Type` はデータ型，`Sort` はその両方を含む一般化です．
`α → β` と `∀ x : α, P x` はどちらも関数型・依存関数型であり，命題として読むと含意や全称量化になります．
`inductive` は constructor で項を作る型を定義し，`structure` は名前つき field をもつ積型を定義し，`class` は `structure` を型クラス探索に登録できる形で定義します．

Chapter 01 で見た `P ∧ Q`，`P ∨ Q`，`∃ x, P x`，`a = b`，`¬ P`，`x ≤ y`，`x < y` は，それぞれ `And`，`Or`，`Exists`，`Eq`，`Not`，`LE.le`，`LT.lt` の notation として理解できます．
それぞれが `structure`，`inductive`，`def`，`class` のどれで実装されているかを見ると，`constructor`，`cases`，`intro`，`rfl`，`rw` などの tactic がどのような証明項を作っているかも見えやすくなります．

今後 Mathlib を読むときには，まず宣言が `def` なのか，`theorem`/`lemma` なのか，`inductive` なのか，`structure` なのか，`class`/`instance` なのかを見ると，対象の役割を把握しやすくなります．
