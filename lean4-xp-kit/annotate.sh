# leanpkg configure
# leanproject get-mathlib-cache

set -e
set -o pipefail

# Install dependencies first
# ./install_deps.sh

export PATH=$HOME/.elan/bin:$PATH

LEAN4_XP_KIT_HOME=../lean4-xp-kit/

renderRst() {
    # echo "${1%.*}"
    filename="${1%.*}"
    alectryon "$filename.lean" --lake lakefile.lean --output-directory dist/
}

renderMd() {
    # echo "${1%.*}"
    filename="${1%.*}"
    # replace "Playground/" with "dist/"
    ofilename="${filename//Playground/dist}"
    echo "Rendering $filename to $ofilename"
    alectryon --frontend lean4+markup "$filename.lean" --backend webpage --lake lakefile.lean -o "$ofilename.md"
    markdown-it "$LEAN4_XP_KIT_HOME/alectryon/header.md" "$ofilename.md" "$LEAN4_XP_KIT_HOME/alectryon/footer.md" > "$ofilename.html"
}

if [[ $2 == "rst" ]]; then
    echo "Rendering RST"
    renderRst "$1"
else
    echo "Rendering MD"
    renderMd "$1"
fi
