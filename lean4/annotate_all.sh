# leanpkg configure
# leanproject get-mathlib-cache

set -e
set -o pipefail

# Install dependencies first
# ./install.sh

# TODO reproduce the problem of not specifying `--lake` and file an issue
alectryon examples/Hello.lean --lake lakefile.lean --output-directory dist/
alectryon examples/LAMR.lean --lake lakefile.lean --output-directory dist/