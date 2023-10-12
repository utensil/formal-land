set -e
set -o pipefail

export PATH="$HOME/.elan/bin:$PATH"

# one of below works
# source ~/.profile
# bash -l

# Install dependencies first

# https://github.com/cpitclaudel/alectryon/issues/83
# https://github.com/leanprover/lean4/blob/master/doc/flake.nix#L11
# python3 -m pip install git+https://github.com/Kha/alectryon.git@typeid
python3 -m pip install git+https://github.com/utensil/alectryon.git@dev

# TODO if leanInk exists and is good, skip this
rm -rf /tmp/leanInk || echo
git clone https://github.com/leanprover/LeanInk /tmp/leanInk -q
cd /tmp/leanInk
lake build

mkdir -p $HOME/.elan/bin
cp /tmp/leanInk/build/bin/* $HOME/.elan/bin

pip install markdown-it-py

# echo You need to run the following command to make leanInk CLI visible to execution
# echo 'export PATH=/tmp/leanInk/build/bin/:$HOME/.elan/bin:$PATH'
