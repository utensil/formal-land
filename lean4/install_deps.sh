set -e
set -o pipefail

export PATH="$HOME/.elan/bin:$PATH"

# one of below works
# source ~/.profile
# bash -l

# Install dependencies first
python3 -m pip install git+https://github.com/cpitclaudel/alectryon.git

# TODO if leanInk exists and is good, skip this
rm -rf /tmp/leanInk || echo
git clone https://github.com/leanprover/LeanInk /tmp/leanInk -q
cd /tmp/leanInk
lake build

echo You need to run the following command to make leanInk CLI visible to execution
echo 'export PATH=/tmp/leanInk/build/bin/:$HOME/.elan/bin:$PATH'
