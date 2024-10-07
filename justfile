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
