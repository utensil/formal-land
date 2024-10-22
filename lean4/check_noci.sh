# leanpkg configure
# leanproject get-mathlib-cache

set -e
set -o pipefail

export PATH=$HOME/.elan/bin:$PATH

echo "checking RockPaperScissor"
lake env lean --quiet --run Playground/NoCI/Zulip/RockPaperScissor.lean < Playground/NoCI/Zulip/RockPaperScissor_test1.txt

