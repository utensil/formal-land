set -e
set -o pipefail

# get git branch name
BRANCH=$(git branch --show-current)

# if branch name starts with v4
if [[ $BRANCH == v4* ]]; then
    echo "leanprover/lean4:$BRANCH" > lean-toolchain
    sed -i 's/^(.*"https:\/\/github\.com\/leanprover-community\/mathlib4").*$/\1 @ leanVersion/g' lakefile.lean
    lake update
    lake build
fi
