#!/usr/bin/env bash

set -e

OWNER=$1
REPO=$2

if [ -z "$OWNER" ] || [ -z "$REPO" ] ; then
    echo "Usage: $0 <owner> <repo>"
    exit 1;
fi
    
default_checkout () {
    echo "Checkout default"
    git clone --recursive https://github.com/${OWNER}/${REPO} ../${REPO}
}

user_branch_checkout () {
    if [ "$2" = "main" ]; then
        default_checkout
    else
        CMD="git ls-remote --heads https://github.com/$1/${REPO} refs/heads/$2"
        echo "Trying: $CMD"
        SEARCH_RES=`$CMD || echo`
        echo "Result: ${SEARCH_RES}"
        if [ -z "${SEARCH_RES}" ]; then
            default_checkout
        else
            echo "Checking out user's branch"
            git clone --recursive https://github.com/$1/${REPO} ../${REPO}
            cd ../${REPO}
            git checkout "$2"
        fi
    fi
}

if [ "${GITHUB_EVENT_NAME}" = "pull_request" ]; then
    if [ -z "${HEAD_OWNER}" ] ; then
        echo "HEAD_OWNER not defined in environment"
        echo "use ${{ github.event.pull_request.head.repo.owner.login }}"
        exit 1
    fi
    user_branch_checkout "${HEAD_OWNER}" "${GITHUB_HEAD_REF}"
elif [ "${GITHUB_EVENT_NAME}" = "push" ]; then
    user_branch_checkout "${GITHUB_ACTOR}" "${GITHUB_REF_NAME}"
else
    echo "GITHUB_EVENT_NAME: ${GITHUB_EVENT_NAME}"
    default_checkout
fi
