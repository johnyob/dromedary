#!/bin/bash

SCRIPT_PATH=$(dirname $0)
CLOC_WITHOUT_EXPECT="$SCRIPT_PATH/cloc-without-expect.txt"

EXCLUDED_DIRS=_build,_coverage,.circleci,.git

echo "Computing line count excluding expect test output ..."

# perform first cloc count w/out expect tests
cloc --force-lang-def=$CLOC_WITHOUT_EXPECT --exclude-dir=EXCLUDED_DIRS "$SCRIPT_PATH/.."


echo "Computing line count including expect test output ..."

cloc --exclude-dir=EXCLUDED_DIRS "$SCRIPT_PATH/.."