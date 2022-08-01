# leanpkg configure
# leanproject get-mathlib-cache

set -e
set -o pipefail

# Install dependencies first
# python3 -m pip install git+https://github.com/cpitclaudel/alectryon.git
# sh -c "$(curl https://raw.githubusercontent.com/leanprover/LeanInk/main/init.sh -sSf)"
# see also https://github.com/leanprover/LeanInk/issues/21 

# TODO reproduce the problem of not specifying `--lake` and file an issue
alectryon examples/Hello.lean --lake lakefile.lean --output-directory dist/
alectryon examples/LAMR.lean --lake lakefile.lean --output-directory dist/