## mdgen + MkDocs site generation

`scripts/build-site.sh` builds the public HTML site from the development repository.

- Human-edited Markdown and static files live in `site-src/`.
- Lean-derived chapter Markdown is generated into `site-generated/`.
- MkDocs input pages are generated into `site-pages/`.
- Static HTML is generated into `docs/`.
- Sidebar entries before and after the generated chapters are controlled by
  `site-src/nav-before.yml` and `site-src/nav-after.yml`.

Initial setup:

```bash
pip install -r requirements-mkdocs.txt
```

Build locally:

```bash
./scripts/build-site.sh
```

Serve locally:

```bash
./scripts/serve-site.sh
```

Do not run `mkdocs serve --livereload` directly from a clean tree: it does not
run `mdgen`, split chapters, or generate `site-pages/print_page.md`.
`scripts/serve-site.sh` defaults to `--no-livereload` because live reload can
race with generated `print_page.md`. Use `SERVE_LIVERELOAD=1` to opt in.
