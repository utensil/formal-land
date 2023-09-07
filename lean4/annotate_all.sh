# leanpkg configure
# leanproject get-mathlib-cache

set -e
set -o pipefail

# Install dependencies first
# ./install.sh

# TODO Warn if /tmp/leanInk/build/bin/ doesn't exist
export PATH=/tmp/leanInk/build/bin/:$HOME/.elan/bin:$PATH

alectryon examples/Hello.lean --lake lakefile.lean --output-directory dist/
alectryon examples/LAMR.lean --lake lakefile.lean --output-directory dist/
alectryon examples/Tactics.lean --lake lakefile.lean --output-directory dist/