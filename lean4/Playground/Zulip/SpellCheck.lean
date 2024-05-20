/-
  This file is also at https://gist.github.com/utensil/9591618f9cf5a0026d3154d062f36c78
-/

/-

This file demonstrates the use of VSCode [Spell Right](https://marketplace.visualstudio.com/items?itemName=ban.spellright)
extension to spell check comments in Lean 4 files while avoiding code or code blocks in comments, it uses some heuristics
to work for both Markdown and [reStructuredText](https://devguide.python.org/documentation/markup/) per request on
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Spell.20check).

The minimal configuration to make it work for Lean is to add the following to your `settings.json` after the installing
the extension, setting up [the spell check dictionaries](https://github.com/bartosz-antosik/vscode-spellright#dictionaries),
and [enable spell check for the language of your choosing](https://github.com/bartosz-antosik/vscode-spellright#changing-language-and-turning-off):

```json
    "spellright.spellContextByClass": { "lean4": "comments" },
    "spellright.parserByClass": {
        "lean4": {
            "parser": "code",
            "comment_start": "/-",
            "comment_end": "-/",
            "comment_line": "--"
        }
    },
    "spellright.notificationClass": "hint",
    "spellright.ignoreRegExpsByClass": {
        "lean4": [
            "/```[^]*?```/gm",
            "/``[^\\n]*?``/g",
            "/`[^\\n]*?`/g",
            "/(?<indentation>[ \\t]*)(?<directiveline>\\.\\. code-block::[^\\n]*\\n)((?<codeline>\\k<indentation>+[ \\t]+[^\\n]*\\n)|(?<emptyline>\\k<indentation>*\\n))*/gm"
        ]
    }
```

-/

/-
  # Tests

  **Expected behavior**: all "axn", "uxn", "txeeet", "whhy" should be marked as misspelled except for the ones in code blocks
  if you have chosen to spell check both English and French.

  This is axn example for `axn`

  Voici uxn exemple pour `uxn`

  `md`: `axn` axn

  `rst`: ``axn`` axn  :source:`PATH`

  ## md code block

  ```lean4
    theorem dummy (axn : Prop) :
        1 + 1 = 2 := by sorry

    This is axn `axn` example
    Voici uxn exemple pour `uxn`

    axn piece of code after axn empty line

  This is axn example for `axn`

  Voici uxn exemple pour `uxn`

  ```

  rst code block
  ------------------

  .. code-block:: axn
    theorem dummy (axn : Prop) :
        1 + 1 = 2 := by sorry

    This is axn `axn` example
    Voici uxn exemple pour `uxn`

    axn piece of code after axn empty line

  normal txeeet with `axn` axn

  whhy

  A single backquote `Name should not affect the following lines

  "axn" should be marked as misspelled

  `axn piece of code` should NOT be marked as misspelled

  ```
    A single backquote `Name in code block should not affect the following lines

    `axn` should NOT be marked as misspelled
  ```

  "axn" should be marked as misspelled

  # The following is a repetition of the above to confirm it works

  **Expected behavior**: all "axn", "uxn", "txeeet", "whhy" should be marked as misspelled except for the ones in code blocks
  if you have chosen to spell check both English and French.

  This is axn example for `axn`

  Voici uxn exemple pour `uxn`

  `md`: `axn` axn

  `rst`: ``axn`` axn  :source:`PATH`

  ## md code block

  ```lean4
    theorem dummy (axn : Prop) :
        1 + 1 = 2 := by sorry

    This is axn `axn` example
    Voici uxn exemple pour `uxn`

    axn piece of code after axn empty line

  This is axn example for `axn`

  Voici uxn exemple pour `uxn`

  ```

  rst code block
  ------------------

  .. code-block:: axn
    theorem dummy (axn : Prop) :
        1 + 1 = 2 := by sorry

    This is axn `axn` example
    Voici uxn exemple pour `uxn`

    axn piece of code after axn empty line

  normal txeeet with `axn` axn

  whhy

  A single backquote `Name should not affect the following lines

  "axn" should be marked as misspelled

  `axn piece of code` should NOT be marked as misspelled

  ```
    A single backquote `Name in code block should not affect the following lines

    `axn` should NOT be marked as misspelled
  ```

  "axn" should be marked as misspelled

-/
theorem dummy (axn : Prop) :
    1 + 1 = 2 := by sorry