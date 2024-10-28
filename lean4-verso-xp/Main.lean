import VersoXp

open Verso.Genre.Manual


def main :=
  manualMain (%doc VersoXp) (config := config)
where
  config := {
    destination := "dist",
    extraFiles := [("static", "static")],
    -- extraCss := ["/static/colors.css", "/static/theme.css", "/static/print.css", "/static/fonts/source-serif/source-serif-text.css", "/static/fonts/source-code-pro/source-code-pro.css", "/static/katex/katex.min.css"],
    -- extraJs := ["/static/katex/katex.min.js", "/static/math.js", "/static/print.js"],
    extraJs := ["/static/math.js"],
    emitTeX := false,
    -- emitHtmlSingle := true, -- for proofreading
    -- logo := some "/static/lean_logo.svg",
    -- sourceLink := some "https://github.com/leanprover/reference-manual",
    -- issueLink := some "https://github.com/leanprover/reference-manual/issues"
  }
