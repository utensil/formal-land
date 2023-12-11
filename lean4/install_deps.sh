set -e
set -o pipefail

if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:v4.2.0-rc1
elif [[ "$OSTYPE" == "darwin"* ]]; then
    brew install elan-init
    elan toolchain install stable
    elan default stable
else
    echo "Unknown OS: $OSTYPE"
    echo "Check out https://leanprover-community.github.io/get_started.html for installation"
    exit 0
fi

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
git clone -b fix-print-path https://github.com/utensil/LeanInk /tmp/leanInk -q
cd /tmp/leanInk
lake build

mkdir -p $HOME/.elan/bin
cp /tmp/leanInk/.lake/build/bin/* $HOME/.elan/bin

pip install markdown-it-py

echo You need to run the following command to make leanInk CLI visible to execution
echo 'export PATH=$HOME/.elan/bin:$PATH'
