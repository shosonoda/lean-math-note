import Mathlib --#
set_option linter.missingDocs false --#

namespace Chapter10 --#

open Lean

/-
# Chapter 10: Lean の仕組み

この章では，Lean を「証明を書くための言語」としてだけでなく，
「ソースコードを読み，エラボレートし，カーネルで検査し，ビルド成果物を作るシステム」として眺めます．

扱う内容は次の通りです．

* Lean の処理パイプライン
* カーネル，エラボレータ，抽象構文木
* `.olean` と `.ilean`
* VS Code を使わずに Lean と相互作用する方法
* プロジェクトのファイル構造と module
* Elan と Lake

参考:

* Lean Language Reference: <https://lean-lang.org/doc/reference/latest/>
* Elaboration and Compilation: <https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/>
* Interacting with Lean: <https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/>
* Source Files and Modules: <https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/>
* Build Tools and Distribution: <https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/>

注意として，Lean Language Reference の `latest` は常に最新系列の Lean を説明しています．
この原稿を書いているプロジェクトの `lean-toolchain` は `leanprover/lean4:v4.30.0` なので，
細かいコマンド出力やビルド成果物の名前は Reference 最新版と少し異なることがあります．
この章では，概念は Reference に沿って説明し，実行例はこのプロジェクトの Lean 4.30.0 で確認できる形にしています．
-/

/-
---
## Lean の処理パイプライン

Lean が `.lean` ファイルを読むときの流れは，大まかには次のようになります．
これは概念図であり，実装が常にこの順にファイル全体を一括処理するという意味ではありません．

```text
文字列としてのソースコード
  ↓ parsing
抽象構文木 Syntax
  ↓ macro expansion
展開後の Syntax
  ↓ elaboration
中核言語の式 Expr
  ↓ kernel checking
カーネルに受理された定義・定理
  ↓ serialization / compilation
.olean, .ilean, C code, native object など
```

実際には，ファイル全体を一度に処理するというより，トップレベルの command ごとに
「構文解析，マクロ展開，エラボレーション，カーネル検査」が進みます．
ある command によって新しい記法や定義が追加されると，次の command はその更新後の環境で解釈されます．

また，マクロ展開はエラボレーションから完全に独立した前処理ではありません．
Reference の言い方では，macro expansion は elaboration の一部であり，
外側の構文を展開してからその層をエラボレートし，内側に残ったマクロはエラボレータがそこに到達したときに展開されます．
したがって，上の図の「macro expansion -> elaboration」は，学習用に分けて見せた模式的な区分です．
-/

#check Lean.Syntax
#check Lean.Expr
#check Lean.Environment

/-
`Syntax` は parser が作る構文木です．
`Expr` はエラボレータが作る，Lean の中核型理論に近い式です．
`Environment` は，これまでに宣言された定義，定理，記法，型クラスインスタンス，属性などを保持する環境です．
実際の対話環境では，これに加えて proof state，識別子の位置，補完候補などの情報も記録され，
VS Code などのフロントエンドがそれを利用します．
-/

/-
---
## 抽象構文木

Lean の parser は，文字列を `Syntax` 型の木に変換します．
これはまだ「意味づけ」されていません．
たとえば `x + y` という構文だけを見ても，自然数の足し算か，群の演算か，行列の足し算かは分かりません．
この段階では，記号の並びとその木構造が分かっているだけです．

Lean では parser や syntax がユーザー拡張可能です．
`notation`，`syntax`，`macro` によって新しい表面構文を追加できます．

各 syntax node には kind があり，エラボレータやマクロ展開器はこの kind を手がかりに処理を選びます．
また，parser から直接作られた syntax には元のソース位置や空白に関する情報も残るため，
エラー表示，hover，ジャンプ，pretty printing などの基礎にもなります．
-/

#check Lean.Syntax.getKind
#check Lean.Parser.runParserCategory

/-
`Syntax.getKind` は syntax node の種類を取り出す関数です．
`Parser.runParserCategory` は，指定した parser category で文字列を解析するための関数です．
通常の証明では直接使いませんが，Lean のフロントエンドが「文字列から syntax tree を作る」ことを確認できます．
-/

/-
---
## マクロ展開とエラボレータ

エラボレーションとは，ユーザー向けの構文を，Lean の中核型理論の式へ変換する処理です．
この処理は単純な翻訳ではありません．
次のような作業も行います．

* 省略された暗黙引数を補う．
* 型を推論する．
* 型クラスインスタンスを探索する．
* overloaded notation の意味を決める．
* tactic script を証明項へ変換する．
* 再帰定義や pattern matching を中核言語が扱える形に変換する．

そのため，エラボレータは Lean の使いやすさの大部分を担っています．
一方で，最終的にできた項はカーネルによって検査されます．

エラボレーションには大きく分けて command elaboration と term elaboration があります．
command elaboration は，`def`，`theorem`，`#check`，`open` などのトップレベル command を処理し，
必要に応じて環境を更新します．
term elaboration は，型注釈，定義の右辺，定理の証明項などを，期待される型の情報も使いながら `Expr` にします．
tactic の実行は term elaboration の特殊な場合と考えられ，最終的には証明項を構成します．
-/

#check Lean.Elab.Command.CommandElabM
#check Lean.Elab.Term.TermElabM
#check Lean.Meta.MetaM

def ch10Double (n : Nat) : Nat :=
  n + n

example : ch10Double 3 = 6 := by
  rfl

#check ch10Double
#reduce ch10Double 3
#eval ch10Double 3

/-
`#check` は型を表示します．
`#reduce` は，定義の展開や再帰子の計算規則など，Lean の definitional equality に関係する簡約で式を正規化します．
`#eval` はコンパイル・実行によって値を表示します．

証明では `#check` で名前の型を調べ，`#reduce` で定義の計算内容を確認し，`#eval` で実行可能なプログラムを試す，という使い分けをします．
`#reduce` と `#eval` はどちらも「計算結果」を見るコマンドですが，前者は証明で使われる簡約の見え方を確認するもの，
後者は実行可能なコードを実際に走らせるもの，と区別しておくとよいです．
-/

set_option pp.all true in
#check (fun n : Nat => n + 1)

/-
`set_option pp.all true` を使うと，pretty printer が通常は隠している情報も多く表示します．
暗黙引数や universe，型クラス引数が見えるため，Lean がどれだけ多くの情報を補っているかを確認できます．
-/

/-
---
## カーネル

Lean の信頼の中心はカーネルです．
カーネルは，エラボレータが作った定義や証明項が，Lean の中核型理論の規則に従っているかを検査します．

重要なのは，tactic やエラボレータは大きく複雑であっても，最終的な証明項はカーネルで検査されるという点です．
したがって，通常の tactic にバグがあっても，間違った証明項を作ればカーネルで拒否されます．

逆に言うと，カーネルは Lean のすべての機能を直接知っているわけではありません．
Reference では，カーネルは中核型理論の type checker であり，構文上の termination checker や unification は含まない，と説明されています．
再帰定義や pattern matching は，エラボレータ側で再帰子，整礎再帰，partial fixpoint などを使う形へ変換されます．
通常の数学的証明で使う定理は最終的にこの検査を通りますが，`partial` や `unsafe` を含むプログラム実行の話は，
論理的な証明項の検査とは分けて理解する必要があります．

ただし，カーネルが検査するのは「形式化された命題が証明されたか」です．
その命題が人間の意図した数学的主張を正しく表しているか，どの公理や imported theorem に依存しているかは別の確認事項です．
-/

#check Eq.refl
#check Nat.rec
#check False

theorem ch10KernelExample (n : Nat) : n = n :=
  Eq.refl n

/-
`Eq.refl n` は等式の反射律を表す証明項です．
`by rfl` のような tactic は，このような証明項を作るための便利な表面構文だと考えられます．
-/

/-
---
## `.olean` と `.ilean`

モジュールをビルドすると，Lean は処理済みの環境情報を `.olean` ファイルに保存します．
import されたモジュールを毎回ソースからエラボレートし直すのではなく，`.olean` を読み込むことで高速に再利用します．

このプロジェクトの Lean 4.30.0 では，言語サーバー用の索引として `.ilean` も生成されます．
これは補完，ジャンプ，情報表示などのためのデータです．
一方，Reference 最新版の module system の説明では，環境は public，private，server 情報に分けて `.olean` として保存される，と説明されています．
つまり，正確なファイル名や分割方法は Lean のバージョンや module system の利用状況に依存します．
授業では「`.olean` は import される検査済み環境，language server 用の情報は対話機能のための補助データ」と押さえれば十分です．
`.ilean` などの中身は実装詳細なので，通常の開発では直接読む対象ではありません．

このプロジェクトで `lake build` を実行すると，典型的には次のようなファイルができます．

```text
.lake/build/lib/lean/LeanMathNote.olean
.lake/build/lib/lean/LeanMathNote.ilean
.lake/build/lib/lean/LeanMathNote/Basic.olean
.lake/build/lib/lean/LeanMathNote/Basic.ilean
```

この章のように `LeanMathNote/gpt/chapter10.lean` を単体で `lake env lean` した場合は，
チェックは行われますが，Lake の通常ビルド対象に入っていなければ `.olean` は残らないことがあります．
-/

/-
---
## VS Code を使わずに Lean と相互作用する

VS Code 拡張は Lean language server の使いやすいフロントエンドです．
しかし，Lean 自体はコマンドラインからも使えます．

このプロジェクトでは，まず `lake env` を付けるのが安全です．
これにより，Mathlib や mdgen など，Lake workspace の依存関係を含んだ環境で `lean` が起動します．

```bash
lake env lean LeanMathNote/gpt/chapter10.lean
lake lean LeanMathNote/gpt/chapter10.lean
lake build
lake exe mdgen LeanMathNote/gpt out/gpt
```

`lean` に直接入力を渡すこともできます．

```bash
printf '#check Nat\n#eval 2 + 3\n' | lake env lean --stdin
```

エラーや情報を機械可読にしたい場合は `--json` が使えます．

```bash
lake env lean --json LeanMathNote/gpt/chapter10.lean
```

language server をエディタなしで起動するには次を使います．

```bash
lake serve
lake env lean --server
```

`lean --server` は LSP クライアントと通信するためのモードです．
人間が直接対話する REPL というより，エディタや外部ツールが Lean と通信するための入口です．
-/

/-
便利な調査コマンドもあります．

```bash
lake env lean --deps LeanMathNote/gpt/chapter10.lean
lake env lean --src-deps LeanMathNote/gpt/chapter10.lean
lake env lean --profile LeanMathNote/gpt/chapter10.lean
lean --print-prefix
lean --print-libdir
lake query LeanMathNote
```

`--deps` は import されるモジュールの依存関係を調べます．
`--profile` は定義や定理ごとの処理時間を見ます．
`--print-prefix` と `--print-libdir` は，現在の Lean toolchain がどこにあるかを確認します．
-/

/-
---
## プロジェクトのファイル構造

Lean プロジェクトは，通常 Lake workspace として管理されます．
このプロジェクトでは，主なファイルは次のような役割を持ちます．

```text
lean-toolchain        使用する Lean toolchain の指定
lakefile.toml         package，依存関係，ライブラリ target の設定
lake-manifest.json    依存パッケージの具体的な revision の固定
LeanMathNote.lean          ライブラリのルート module
LeanMathNote/              Lean ソースファイル
LeanMathNote/gpt/          講義資料用の Lean ファイル
out/                  mdgen によって生成される Markdown
.lake/                Lake が管理する依存関係とビルド成果物
```

`lake-manifest.json` は依存関係のバージョンを固定するため，通常はソース管理に含めます．
一方，`.lake/` はビルド成果物やダウンロード済み依存関係を含む作業ディレクトリなので，普通はソース管理に含めません．
-/

/-
---
## module と import

Lean のファイルは import 可能な単位として扱われます．
import で使う module 名は，ソースルートからのパスに対応します．

たとえば次のように対応します．

```text
LeanMathNote.lean                 module LeanMathNote
LeanMathNote/Basic.lean           module LeanMathNote.Basic
LeanMathNote/BasicMdgen.lean      module LeanMathNote.BasicMdgen
LeanMathNote/gpt/chapter10.lean   module LeanMathNote.gpt.chapter10
```

別の module を使うには，ファイル冒頭で `import` します．

```lean
import Mathlib
import LeanMathNote.Basic
```

`import Mathlib` は Mathlib 全体を読み込むので講義資料では便利です．
実際の大きな開発では，ビルド時間を抑えるために必要な module だけを import します．
-/

/-
Lean Reference 最新版では，`module` header を使った module system のもとで，
`public`，`private`，`import all`，`@[expose]` などによって公開範囲や定義本体を展開できる範囲を制御する話も出てきます．
これは，ほかの module から名前を参照できるか，定義本体を unfolding できるか，変更時にどこまで再ビルドが必要になるかに関係します．
通常の Mathlib 利用やこの講義資料では，まず「ファイルパスと import 名の対応」と `namespace` の違いを理解すれば十分です．
-/

namespace ModuleExample

def localDefinition : Nat :=
  10

example : localDefinition = 10 := by
  rfl

end ModuleExample

/-
`namespace` は module とは別の仕組みです．
module はファイル単位の読み込み単位で，namespace は名前の階層を作る仕組みです．
同じ module の中に複数の namespace を置くことも，複数の module に同じ namespace の定義を分散させることもできます．
-/

/-
---
## Elan

Elan は Lean toolchain manager です．
`lean`，`lake`，`leanchecker` などのコマンドは，Elan の proxy 経由で現在のプロジェクトに合った toolchain を呼び出します．

現在のプロジェクトでは，`lean-toolchain` に次のような指定があります．

```text
leanprover/lean4:v4.30.0
```

このファイルにより，プロジェクトに入って `lean` や `lake` を実行したときに，対応する Lean 4.30.0 の toolchain が使われます．
複数人で開発するとき，全員が同じ Lean version と Mathlib revision を使うために重要です．

よく使う Elan コマンドは次の通りです．

```bash
elan show
elan toolchain list
elan toolchain install leanprover/lean4:v4.30.0
elan default leanprover/lean4:stable
```

特定のコマンドだけ別 toolchain で実行するには，`+` を使います．

```bash
lake +leanprover/lean4:v4.30.0 build
```
-/

/-
---
## Lake

Lake は Lean の標準ビルドツールです．
主な役割は次の通りです．

* package の設定を読む．
* 依存関係を取得・固定する．
* module の依存関係を追跡して増分ビルドする．
* `.olean`，言語サーバー用の索引，C code，実行ファイルなどの成果物を作る．
* executable や script を実行する．

このプロジェクトの `lakefile.toml` には，次のような情報が書かれています．

```toml
name = "lean-math-note"
defaultTargets = ["LeanMathNote"]

[[lean_lib]]
name = "LeanMathNote"

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.30.0"
```

`[[lean_lib]]` は Lean library target を定義します．
`[[require]]` は依存パッケージを定義します．
`lake-manifest.json` は，それらの依存関係を具体的な git revision に固定します．
-/

/-
よく使う Lake コマンドです．

```bash
lake update          # 依存関係を更新し，manifest を更新する
lake build           # default target をビルドする
lake build LeanMathNote   # target を明示してビルドする
lake env lean ...    # workspace の環境で lean を実行する
lake exe mdgen ...   # executable をビルドして実行する
lake clean           # build outputs を削除する
lake serve           # Lean language server を起動する
```

この講義資料では `lake exe mdgen LeanMathNote/gpt out/gpt` により，
`LeanMathNote/gpt/` 配下の `.lean` ファイルから Markdown を生成しています．
-/

/-
---
## `leanchecker`

通常の開発では，`lean` や `lake build` によって各宣言がカーネルで検査されます．
さらに `.olean` に保存された環境を再検査するための道具として `leanchecker` があります．

概念的には，次のように使います．

```bash
leanchecker .lake/build/lib/lean/LeanMathNote.olean
```

通常の授業や演習ではここまで行う必要はありません．
ただし，「Lean の信頼は最終的に小さなカーネル検査に帰着する」という話をするときに，
`.olean` と `leanchecker` は重要なキーワードです．
-/

/-
---
## まとめ

Lean の仕組みを理解するうえで，次の対応を押さえておくと見通しがよくなります．

* parser は文字列を `Syntax` にする．
* macro expansion は表面構文をより基本的な構文へ変換する．実際には elaboration と相互に入り組んで進む．
* elaborator は `Syntax` を型つきの `Expr` にし，暗黙引数，型クラス，tactic，再帰定義などを処理する．
* kernel は `Expr` が中核型理論の規則に従うかを検査する．
* `.olean` は検査済み環境を保存し，import を高速化する．
* このプロジェクトの Lean 4.30.0 では `.ilean` が language server のための索引として生成される．
* Elan は toolchain のバージョンを選ぶ．
* Lake は package，依存関係，module，ビルド成果物を管理する．

普段の証明では，これらをすべて意識する必要はありません．
しかし，エラーの原因を切り分けるとき，依存関係を管理するとき，AI や外部ツールから Lean を呼び出すときには，この構造を知っていることが役に立ちます．
-/
/-
---
## 演習問題

この章の演習では，Lean の内部構造とコマンドライン操作を確認します．
証明を作るだけでなく，実際にターミナルでコマンドを実行して出力を読むことを目標にしてください．

1. 次のコマンドを実行し，Lean のバージョンと toolchain を確認してください．

```bash
lean --version
lake --version
elan show
cat lean-toolchain
```

2. VS Code を使わずに，この章を単体でチェックしてください．

```bash
lake env lean LeanMathNote/chapter10.lean
lake lean LeanMathNote/chapter10.lean
```

3. 標準入力から Lean にコードを渡してください．

```bash
printf '#check Nat\n#eval 2 + 3\n' | lake env lean --stdin
```

4. `--json` を付けて Lean を実行し，通常の出力との違いを確認してください．

```bash
lake env lean --json LeanMathNote/chapter10.lean
```

5. `--deps` と `--src-deps` を使って，依存関係の出力を比較してください．

```bash
lake env lean --deps LeanMathNote/chapter10.lean
lake env lean --src-deps LeanMathNote/chapter10.lean
```

6. `Syntax`，`Expr`，`Environment` の型を確認してください．

```lean
#check Lean.Syntax
#check Lean.Expr
#check Lean.Environment
```

7. pretty printer の出力を詳しくして，暗黙引数や型クラス引数が表示されることを確認してください．

```lean
set_option pp.all true in
#check (fun n : Nat => n + 1)
```

8. `lake build` を実行した後，生成される `.olean` と `.ilean` を探してください．

```bash
lake build
find .lake/build/lib -name '*.olean' | head
find .lake/build/lib -name '*.ilean' | head
```

9. module 名とファイルパスの対応を説明してください．

```text
LeanMathNote.lean
LeanMathNote/chapter01.lean
LeanMathNote/chapter10.lean
```

10. `lakefile.toml` を読み，`[[lean_lib]]` と `[[require]]` が何を指定しているか説明してください．
-/

end Chapter10 --#
