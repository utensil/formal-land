set -e
set -o pipefail

# get git branch name
BRANCH=$(git branch --show-current)

# if branch name starts with v4
if [[ $BRANCH == v4* ]]; then
    echo "leanprover/lean4:$BRANCH" > lean-toolchain
    cat lean-toolchain
    # rm -rf .lake
    # rm -f lake-manifest.json
    lake -R -Kenv=dev update
fi
