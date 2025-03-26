default:
    just --list

@jobs:
    # use gh api to query all latest successful workflow run
    # then use jq to filter path contains lean4.yml then extract the job id
    gh api \
        -H "Accept: application/vnd.github+json" \
        -H "X-GitHub-Api-Version: 2022-11-28" \
        '/repos/utensil/formal-land/actions/runs?branch=main&status=success&per_page=50' \
        -q '.workflow_runs[] | select(.path | contains("lean4.yml")) | .id'|head -n 1 # ,.path,' # select(.path | contains("lean4.yml")) | .jobs[0].id'

@pages DIR:
    mkdir -p github-pages
    rm -rf ./github-pages/{{DIR}}
    mv ./{{DIR}}/dist ./github-pages/{{DIR}}
    ls -R ./github-pages/

@copy-assets:
    mkdir -p github-pages
    cp -r assets/* github-pages/

@check-pages:
    #!/usr/bin/env bash
    missing_dirs=()
    for dir in aya lean4 tla; do
        if [ ! -d "github-pages/$dir" ]; then
            missing_dirs+=("$dir")
        fi
    done
    if [ ${#missing_dirs[@]} -ne 0 ]; then
        echo "Missing directories: ${missing_dirs[*]}"
        exit 1
    fi

[no-cd]
@annotate LIB_DIR:
    #!/usr/bin/env bash
    ../lean4-xp-kit/install_deps.sh
    ../lean4-xp-kit/annotate_all.sh {{LIB_DIR}}
   

@lake-new NAME VERSION="v4.11.0":
    #!/usr/bin/env bash
    lake +leanprover/lean4:{{VERSION}} new {{NAME}}
    cd {{NAME}}
    mkdir less
    mv .git less/
    mv .github less/
    mv .gitignore less/
    cd ..
    mv {{NAME}} lean4-{{NAME}}

[no-cd]
prep-py:
    #!/usr/bin/env bash
    uv venv --python 3.11 --seed
    source .venv/bin/activate
    ./install_deps.sh

prep-lean:
    curl https://elan.lean-lang.org/elan-init.sh -sSf | bash -s -- -y

bump:
  #!/usr/bin/env bash
  cd lean4
  ./switch.sh

[no-cd]
clean:
    rm -rf .lake
    lake -R clean

[no-cd]
up *NAME:
    lake -R update {{NAME}}
    lake -R build

[no-cd]
build:
    lake -R exe cache get
    lake -R build

[no-cd]
test:
    lake -R test

[no-cd]
vsgen:
    lake -R exe mkVersoDoc
    rm -rf dist
    mv _out/html-multi dist

[no-cd]
vs: vsgen
    open dist/index.html
