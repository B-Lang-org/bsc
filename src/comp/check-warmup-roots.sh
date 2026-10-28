#!/usr/bin/env bash
# Every root module of the compiler's build must import Warmup. A root is a
# module whose imports name no other module of the build; nothing makes it
# compile after Warmup, so the barrier Warmup.hs provides for a deterministic
# parallel build (see its header) reaches it only through its own import.
# The generated modules (Warmup, BuildVersion, BuildSystem) do not count as
# imports of the build, so a clean tree and a built one give the same
# answer. Exits 1 naming the roots that lack the import.
set -euo pipefail
cd "$(dirname "$0")/../.."
dirs="src/comp src/Parsec src/vendor/htcl src/vendor/stp/HaskellIfc src/vendor/yices/v2.6/HaskellIfc"
find $dirs \( -name '*.hs' -o -name '*.lhs' \) -exec awk '
BEGIN { generated["Warmup"]; generated["BuildVersion"]; generated["BuildSystem"] }
FNR == 1 { file = FILENAME; sub(/\.l?hs$/, "", file); n = split(file, p, "/"); name[FILENAME] = p[n] }
# the declared module name (hierarchical ones live under src/comp/Parser)
/^>?[ \t]*module[ \t]+[A-Z][A-Za-z0-9_.\047]*/ && !(FILENAME in declared) {
    s = $0; sub(/^>?[ \t]*module[ \t]+/, "", s); sub(/[^A-Za-z0-9_.\047].*$/, "", s); declared[FILENAME] = 1; name[FILENAME] = s
}
/^>?[ \t]*import[ \t]/ {
    s = $0; sub(/^>?[ \t]*import[ \t]+/, "", s)
    sub(/^\{-#[^#]*#-\}[ \t]*/, "", s); sub(/^safe[ \t]+/, "", s); sub(/^qualified[ \t]+/, "", s); sub(/^"[^"]*"[ \t]+/, "", s)
    sub(/[^A-Za-z0-9_.\047].*$/, "", s)
    if (s != "") imports[FILENAME, s] = 1
}
END {
    for (f in name) modules[name[f]] = f
    for (f in name) {
        m = name[f]
        if (m in generated) continue
        root = 1
        for (key in imports) { split(key, k, SUBSEP); if (k[1] != f) continue
            if ((k[2] in modules) && !(k[2] in generated)) { root = 0; break } }
        if (!root) continue
        roots++
        if (!((f, "Warmup") in imports)) { missing++; print "root module without import Warmup: " f }
    }
    printf "%d modules, %d roots, %d without import Warmup\n", length(name), roots, missing + 0 > "/dev/stderr"
    exit missing > 0
}' {} + | LC_ALL=C sort
