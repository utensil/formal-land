# leanpkg configure
# leanproject get-mathlib-cache

set -e
set -o pipefail

# Install dependencies first
# ./install_deps.sh

# TODO Warn if /tmp/leanInk/build/bin/ doesn't exist
# export PATH=/tmp/leanInk/build/bin/:$HOME/.elan/bin:$PATH

export PATH=$HOME/.elan/bin:$PATH

mkdir -p dist/Zulip/
mkdir -p dist/NoCI/

cp ../lean4-xp-kit/alectryon/*.css dist/
cp ../lean4-xp-kit/alectryon/*.js dist/

lake -R exe annotate "${1:-Playground}" --verbose 2>/dev/null

cp dist/*.css dist/Zulip/
cp dist/*.js dist/Zulip/

# renderMd NoCI/Arrow.lean
# cp dist/NoCI/Arrow.* dist/Zulip/
