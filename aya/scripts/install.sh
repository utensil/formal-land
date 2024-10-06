#!/bin/bash

# adapted from https://www.aya-prover.org/guide/install.html#download-from-github-release

AYA_PREFIX=${AYA_PREFIX:-~/.aya}

#check if the variable $AYA_PREFIX is not empty
if [ -z "$AYA_PREFIX" ]; then
    echo "AYA_PREFIX is empty"
    exit 1
else
    echo "AYA_PREFIX is set to '$AYA_PREFIX'"
fi

AYA_OS="unknown"

# detect OS
if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    echo "Linux detected"
    AYA_OS="linux"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    echo "MacOS detected"
    AYA_OS="macos"
else
    echo "Unsupported OS"
    exit 1
fi

AYA_ARCH="unknown"

# detect architecture
if [ $(uname -m) == "x86_64" ]; then
    echo "x86_64 detected"
    AYA_ARCH="x64"
elif [ $(uname -m) == "arm64" ]; then
    echo "arm64 detected"
    AYA_ARCH="aarch64"
else
    echo "Unsupported architecture"
    exit 1
fi

rm -rf ${AYA_PREFIX:-~/.aya}
mkdir -p ${AYA_PREFIX}
chown $USER ${AYA_PREFIX}
cd ${AYA_PREFIX}
AYA_ZIP=aya-prover_jlink_${AYA_OS}-${AYA_ARCH}.zip
wget https://github.com/aya-prover/aya-dev/releases/download/nightly-build/$AYA_ZIP -O ${AYA_PREFIX}/$AYA_ZIP
unzip -o $AYA_ZIP
rm $AYA_ZIP

echo >> ~/.bashrc
echo "export AYA_PREFIX=${AYA_PREFIX}" >> ~/.bashrc
echo 'export PATH="$AYA_PREFIX/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc

echo >> ~/.zshrc
echo "export AYA_PREFIX=${AYA_PREFIX}" >> ~/.zshrc
echo 'export PATH="$AYA_PREFIX/bin:$PATH"' >> ~/.zshrc
source ~/.zshrc

echo 'Run `source ~/.bashrc` or `source ~/.zshrc` to start using Aya Prover'