# leanpkg configure
# leanproject get-mathlib-cache

set -e
set -o pipefail

# Install dependencies first
# ./install_deps.sh

# TODO Warn if /tmp/leanInk/build/bin/ doesn't exist
# export PATH=/tmp/leanInk/build/bin/:$HOME/.elan/bin:$PATH

export PATH=$HOME/.elan/bin:$PATH

renderRst() {
    # echo "${1%.*}"
    filename="${1%.*}"
    alectryon examples/$filename.lean --lake lakefile.lean --output-directory dist/ --traceback
}

renderMd() {
    # echo "${1%.*}"
    filename="${1%.*}"
    alectryon --frontend lean4+markup examples/$filename.lean --backend webpage --lake lakefile.lean -o dist/$filename.md --traceback
    markdown-it alectryon/header.md dist/$filename.md alectryon/footer.md > dist/$filename.html
}

# alectryon examples/Hello.lean --lake lakefile.lean --output-directory dist/
# alectryon examples/LAMR.lean --lake lakefile.lean --output-directory dist/
# alectryon examples/Tactics.lean --lake lakefile.lean --output-directory dist/

# # https://github.com/leanprover/lean4/blob/master/doc/flake.nix#L89
# alectryon --frontend lean4+markup examples/HelloMarkdown.lean --backend webpage --lake lakefile.lean -o dist/HelloMarkdown.md
# markdown-it alectryon/header.md dist/HelloMarkdown.md alectryon/footer.md > dist/HelloMarkdown.html

# TODO
# for file in example/*.lean; do
#   renderMd "$file"
# done

renderRst Hello.lean
renderRst LAMR.lean
renderRst Tactics.lean

renderMd Branch.lean
renderMd Cat.lean
renderMd Chisolm.lean
renderMd Filters.lean
renderMd FiltersMWE.lean
renderMd FiniteGroup.lean
renderMd HelloMarkdown.lean
renderMd Help.lean
renderMd Hierarchies.lean
renderMd index.lean
renderMd MV.lean
renderMd Rank.lean

renderMd index.lean

mkdir -p dist/Zulip/
mkdir -p dist/NoCI/

cp dist/*.css dist/Zulip/
cp dist/*.js dist/Zulip/

renderMd Zulip/Agatha.lean
renderMd Zulip/Arrow.lean
renderMd Zulip/Calc.lean
renderMd Zulip/Closed.lean
renderMd Zulip/EnvExt.lean
renderMd Zulip/Have.lean
renderMd Zulip/Heartbeat.lean
renderMd Zulip/Import.lean
renderMd Zulip/Infix.lean
renderMd Zulip/LFTCM2023.lean
renderMd Zulip/Monad.lean
renderMd Zulip/Rintro.lean
renderMd Zulip/SlimCheck.lean
renderMd Zulip/SmallStep.lean
renderMd Zulip/SpellCheck.lean
renderMd Zulip/WithLog.lean

# renderMd NoCI/Arrow.lean
# cp dist/NoCI/Arrow.* dist/Zulip/
