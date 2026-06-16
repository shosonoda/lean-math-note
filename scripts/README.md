## mdgen + MkDocs による静的html生成スクリプト

`LeanMathNote/*.lean` から `mdgen` で Markdown を生成し，`site-src/` の材料と合わせて MkDocs Material で `docs/` に静的HTMLを生成する．

- 初回のみ
  ```bash
  pip install mkdocs-material "requests>=9.7,<10"
  ```
- ローカルビルド・確認
  ```bash
  ./scripts/build-site.sh
  mkdocs serve --livereload
  ```
- 生成物
  - `site-src/chapter*.md`: `mdgen` による生成 Markdown
  - `site-pages/`: `---` によるページ分割後の MkDocs 入力用 Markdown
  - `site-pages/print_page.md`: 印刷用に全ページ本文を 1 本に連結した Markdown
  - `docs/`: MkDocs による HTML 一式
