# レポート課題

- 提出期限
    - 2026年7月31日（金）23:59まで
- 提出方法
    - 学籍番号と氏名，解いた問題を明記すること．
    - Lean Project: 以下のいずれか．
        - [Lean Playground](https://live.lean-lang.org/) に動作確認済の Lean コードを貼り付けて，そのリンクを共有
            - 例:
      <https://live.lean-lang.org/#codez=PQWgUIZtqLI%2BhWro78oC4AEBBAQgYQIwCYDMALCAKxiDwNoLAqygYC6AoHoFSagcwlgjBgCWAtgA4D2ATgBckAWQCGggBYAbdgCMwYKQFMByzqICeAZTE9pygCqTV%2FdUgAUAOyTIAchICUtpFYDUNgLxIcSAFSutt5ymmBISADm%2FOxWACZgQA>

        - Lean Project を格納した public GitHubリポジトリを作成し，そのリンクを共有
            - 例:
      <https://github.com/shosonoda/lean-math-note/>

    - 論述問題
        - 電子ファイルを提出


## 問題
以下のいずれか一方を選んで回答せよ．両方回答した場合はそれぞれの得点の高い方で採点する．

1. 好きな数学定理とその証明を形式化した Lean Project を作成せよ．以下の要件を満たす方が望ましい．
    1. `sorry` を含まないこと
    2. `lake build` を実行し，ビルドが成功すること
    3. 問題選定の観点，形式化の難しさや面白さ，形式化の方法，その他の工夫などを説明したドキュメントをつけること

    - 備考:
        - Lean Projects の具体例は [Reservoir](https://reservoir.lean-lang.org/packages) にインデックスされている．
        - [Aristotle](https://aristotle.harmonic.fun/) などの専用AIを利用してもよい．

1. 論述問題
    1. Lean ではどのように主張の正しさを保証しているのか説明せよ
    2. Lean で形式的な証明が通っているにも関わらず，その意味は必ずしも「正しくない」主張として解釈できる定理の例を一つ挙げ，その仕組みを説明せよ
