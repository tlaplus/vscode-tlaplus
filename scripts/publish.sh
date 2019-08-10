#!/bin/bash

function print_error {
    echo
    echo "Error: $1"
    echo
}

cd "$(dirname "$0")"
VERSION="$(./version.sh)"

if [ -z "$VERSION" ]; then
    print_error 'Cannot extract the extension version number. Publication aborted.'
    exit 1
fi

echo
read -p "Version $VERSION is to be published. Enter \`yes\` to continue: " ANS
if [ $ANS != "yes" ]; then
   echo 'Publication cancelled.'
   exit 2
fi

cd ..
TAG="v$VERSION"

echo "Building .vsix..."
vsce package --baseContentUrl --baseImagesUrl
VSCE_CODE=$?
if [ $VSCE_CODE -ne 0 ]; then
    print_error "Cannot build .vsix file, exit code $VSCE_CODE. Publication aborted."
    exit 3
fi

echo "Creating version tag..."
git tag -a "$TAG" -m "Version $VERSION" && git push origin "$TAG"

exit 0
