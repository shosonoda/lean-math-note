# 数学系エンドユーザーのためのLean入門

「数学系エンドユーザーのためのLean入門」の講義資料です．

- 講義概要:
    - [https://www.math.kyoto-u.ac.jp/ja/event/seminar/6028](https://www.math.kyoto-u.ac.jp/ja/event/seminar/6028)
- 講義資料:
    - [https://shosonoda.github.io/lean-math-note/](https://shosonoda.github.io/lean-math-note/)
    - [https://github.com/shosonoda/lean-math-note/](https://github.com/shosonoda/lean-math-note/)
- 環境構築:
    - [https://shosonoda.github.io/lean-install/](https://shosonoda.github.io/lean-install/)
- 担当:
    - [園田翔（理化学研究所 / サイバーエージェント）](https://sites.google.com/view/shosonoda/home)

## 使い方
GitHubリポジトリをローカルに clone
```bash
git clone https://github.com/shosonoda/lean-math-note.git
```
プロジェクトルートで Lean バージョン確認
```bash
cd lean-math-note
cat lean-toolchain
elan show | grep -A 5 "active toolchain"
```
キャッシュ取得後，ビルド
```bash
lake exe cache get
lake build
```
VS Code 起動
```bash
code .
```
