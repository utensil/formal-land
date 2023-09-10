set -e
set -o pipefail

# TODO if lake-manifest.json doesn't exist
# lake update
lake exe cache get
lake build