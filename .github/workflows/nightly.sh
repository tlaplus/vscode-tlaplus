#!/bin/bash

# Switch to nightly

# Calculate version
VERSION=`git log -1 --format=%cd --date="format:%Y.%-m.%-d%H"`
COMMIT=`git log -1 --format=%H`

# Change parameters in package.json
(cat package.json | jq --indent 4 --arg VERSION "${VERSION}" '
.version=$VERSION |
.preview=true |
.name="vscode-tlaplus-nightly" |
.displayName="TLA+ Nightly" |
.description="TLA+ language support (Nightly)" |
.icon="resources/images/tlaplus-nightly.png"
') > /tmp/package.json.nightly && mv /tmp/package.json.nightly package.json

# Add version info to CHANGELOG.md
printf "## ${VERSION}\n\nCommit ${COMMIT}\n\n" | cat - CHANGELOG.md > /tmp/CHANGELOG.md.nightly && mv /tmp/CHANGELOG.md.nightly CHANGELOG.md

# Add header to README.md
tail -n +2 README.md | cat README-nightly.md - > /tmp/README.md.nightly && mv /tmp/README.md.nightly README.md 
