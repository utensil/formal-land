# leanpkg configure
# leanproject get-mathlib-cache

set -e
set -o pipefail

# Install dependencies first
# ./install_deps.sh

export PATH=$HOME/.elan/bin:$PATH

renderRst() {
    # echo "${1%.*}"
    filename="${1%.*}"
    alectryon examples/$filename.lean --lake lakefile.lean --output-directory dist/
}

renderMd() {
    # echo "${1%.*}"
    filename="${1%.*}"
    alectryon --frontend lean4+markup examples/$filename.lean --backend webpage --lake lakefile.lean -o dist/$filename.md
    markdown-it alectryon/header.md dist/$filename.md alectryon/footer.md > dist/$filename.html
}

renderMd $1
