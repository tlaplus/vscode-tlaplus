#!/bin/bash
# Extracts the extension version number from package.json
PACKAGE_JSON="$(dirname "$0")"/../package.json
grep -o '"version":\s\+"\(.\+\)"' $PACKAGE_JSON | sed 's/"version": "\(.*\)"/\1/'
