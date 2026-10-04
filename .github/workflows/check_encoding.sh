#!/usr/bin/env bash

set -e

SCRIPTDIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

RESULT=0

# -----
# Check that all text files in the repo are valid UTF-8 (of which plain
# ASCII is a subset).  BSC itself rejects non-UTF-8 source files (error
# P0224), and a mix of encodings in the repo confuses tools and editors.
#
# Files can be exempted from the check by listing their exact paths in
# 'allow_non_utf8.files'.  The exempted files are testsuite fixtures for
# BSC's rejection of non-UTF-8 input, so they are additionally required
# to NOT be valid UTF-8; that way a well-intentioned transcoding sweep
# cannot silently defeat those tests.

ALLOWFILE=${SCRIPTDIR}/allow_non_utf8.files

declare -A ALLOW
while IFS= read -r LINE || [ -n "$LINE" ]; do
    case $LINE in
        ''|'#'*) continue ;;
    esac
    ALLOW[$LINE]=notseen
done < "$ALLOWFILE"

# Classify files with 'git ls-files --eol': the index eolinfo ('i/' field)
# is '-text' for files that git considers binary (a NUL byte anywhere in
# the content) and empty for symlinks and submodules; everything else is
# text that must decode as UTF-8.  Validation uses iconv rather than
# 'file --mime-encoding', because 'file' only examines the beginning of
# large files.  Converting to UTF-32LE (rather than to UTF-8) matters:
# glibc iconv's UTF-8 decoder accepts 5-byte sequences and codepoints
# beyond U+10FFFF that strict decoders (including BSC's) reject, but its
# UTF-32LE converter rejects them.

TEXTFILES=()
while IFS= read -r -d '' ENTRY; do
    INFO=${ENTRY%%$'\t'*}
    FILE=${ENTRY#*$'\t'}
    EOLINFO=${INFO%% *}
    if [ -n "${ALLOW[$FILE]}" ]; then
        ALLOW[$FILE]=seen
        continue
    fi
    case $EOLINFO in
        i/) continue ;;
        i/-text)
            # NUL bytes make git classify UTF-16/32 text as binary, so it
            # would otherwise skip validation entirely; catch the common
            # byte-order-mark case
            case $(head -c 2 -- "$FILE" | od -An -tx1 | tr -d ' \n') in
                fffe|feff)
                    echo "$FILE: looks like UTF-16/32 text (byte order mark), not UTF-8"
                    RESULT=1 ;;
            esac
            continue ;;
    esac
    TEXTFILES+=("$FILE")
done < <(git ls-files --eol -z)

# 'git ls-files' failures are invisible through the process substitution,
# but they would leave this list empty

if [ ${#TEXTFILES[@]} -eq 0 ]; then
    echo "No text files found -- did 'git ls-files' fail?"
    RESULT=1
fi

# Quick pass: validate all files in a few batched iconv calls.  Only if
# something fails, rescan one file at a time to report the offenders.

if [ ${#TEXTFILES[@]} -ne 0 ] &&
   ! printf '%s\0' "${TEXTFILES[@]}" \
     | xargs -0 -r iconv -f UTF-8 -t UTF-32LE -- > /dev/null 2> /dev/null; then
    for FILE in "${TEXTFILES[@]}"; do
        if ! iconv -f UTF-8 -t UTF-32LE -- "$FILE" > /dev/null 2> /dev/null; then
            echo "$FILE: not valid UTF-8"
            RESULT=1
        fi
    done
fi

# -----
# The exempted files must exist and must really be non-UTF-8

for FILE in "${!ALLOW[@]}"; do
    if [ "${ALLOW[$FILE]}" != seen ]; then
        echo "$FILE: listed in allow_non_utf8.files but not a tracked file"
        RESULT=1
    elif iconv -f UTF-8 -t UTF-32LE -- "$FILE" > /dev/null 2> /dev/null; then
        echo "$FILE: is valid UTF-8, but files in allow_non_utf8.files must not be (they test BSC's encoding error)"
        RESULT=1
    fi
done

# -----

if [ "$RESULT" -ne 0 ]; then
    echo "Encoding problems found!"
fi

exit $RESULT
