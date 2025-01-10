git ls-files 'ZKLib/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > ZKLib.lean
# git ls-files 'Examples/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Examples.lean
