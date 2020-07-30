#!/usr/bin/env bash
set -x

OS=$1

CURL() {
    # Don't print progress bar
    # Show HTTP request/response ouput (for debugging)
    # Follow HTTP 301 redirects
    # Retry on temporary failures
    # On permanent errors exit with non-zero exit code
    # Use a GitHub token so we don't hit rate limits, and can download artifacts
    curl --silent \
         --verbose \
         --location \
         --retry 3 \
         --fail \
         --header "Authorization: Bearer $TOKEN" \
         "$@"
}

# Get the artifacts_url from the most recent successful continuous integration
# build triggered by a push to the master branch on B-Lang-org/bsc.
API=https://api.github.com/repos/B-Lang-org/bsc
LATEST_PUSH="event=push&branch=master&status=success&per_page=1"

if CURL "$API/actions/workflows/build.yml/runs?$LATEST_PUSH" --output runs.json; then
    ARTIFACTS=$(jq -r '.workflow_runs[0].artifacts_url' < runs.json)
else
    echo Failed to get workflow runs
    cat runs.json
    exit 1
fi


# Find the artifact for the specified OS build
if CURL "$ARTIFACTS" --output artifact.json; then
    DOWNLOAD_URL=$(jq -r '.artifacts[] | select(.name=="'$OS' build") .archive_download_url' < artifact.json)
else
    echo Failed to get latest artifacts
    cat artifact.json
    exit 1
fi

# Download the artifact. Note that unlike the above API methods, this requires
# an authorization token that has at least public repo access. Use the token
# created for github actions
# See https://help.github.com/en/actions/configuring-and-managing-workflows/authenticating-with-the-github_token
if CURL "$DOWNLOAD_URL" --output inst.zip; then
    # The zip file contains a single tarball...
    unzip inst.zip

    # Install bsc into a sibling bsc dir that the testsuite automatically finds.
    mkdir ../bsc
    tar  -C../bsc/ -zxf inst.tar.gz
    rm inst.zip inst.tar.gz
else
    echo Failed to download bsc toolchain
    exit 1
fi
