# leanpkg configure
# leanproject get-mathlib-cache

set -e
set -o pipefail

# Install dependencies first
# ./install_deps.sh

# TODO Warn if /tmp/leanInk/build/bin/ doesn't exist
# export PATH=/tmp/leanInk/build/bin/:$HOME/.elan/bin:$PATH

export PATH=$HOME/.elan/bin:$PATH

alectryon examples/Hello.lean --lake lakefile.lean --output-directory dist/
alectryon examples/LAMR.lean --lake lakefile.lean --output-directory dist/
alectryon examples/Tactics.lean --lake lakefile.lean --output-directory dist/

# https://github.com/leanprover/lean4/blob/master/doc/flake.nix#L89
alectryon --frontend lean4+markup examples/HelloMarkdown.lean --backend webpage --lake lakefile.lean -o dist/HelloMarkdown.md
markdown-it alectryon/header.md dist/HelloMarkdown.md alectryon/footer.md > dist/HelloMarkdown.html