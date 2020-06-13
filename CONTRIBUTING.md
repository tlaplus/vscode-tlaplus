All forms of contribution are highly welcome! Feel free to file bugs, propose improvements, ask questions, send other feedback.

For those, who whant to write some code, here's a short guide.

# Getting started

## Prerequisites

1. Since this is a VS Code extension, you'll need [VS Code](https://code.visualstudio.com/) to check your fixes and improvements.
2. The extension requires [NodeJS](https://nodejs.org/en/) runtime (12.12 at the moment).
3. It's written mostly in [TypeScript](https://www.typescriptlang.org), so you'll need to install it too.

## Clone, Build, Test

Clone the repository:

```
git clone https://github.com/alygin/vscode-tlaplus.git
cd vscode-tlaplus
```

Download dependencies:

```
npm install
```

Build, check and test:

**Warning!** VS Code must not be open when you run tests from command line.

```
npm run vscode:prepublish
npm run lint
npm test
```

## Run and Debug

To run the extension in debug mode:

1. Open the project directory in VS Code.
2. Switch to the [Debug and Run](https://code.visualstudio.com/docs/editor/debugging) panel.
3. Select the "Extension" config.
4. Press "Start Debugging".

Or just use a hotkey for the `Start Debugging` command if the "Extension" configuration is already selected.

## Test from VS Code

To run unit tests from VS Code:

1. Open the project directory in VS Code.
2. Switch to the [Debug and Run](https://code.visualstudio.com/docs/editor/debugging) panel.
3. Select the "Run Extension Tests" config.
4. Press "Start Debugging".

Or just use a hotkey for the `Start Debugging` command if the "Run Extension Tests" configuration is already selected.

# Overview

The extension consists of the following components:

1. Language definitions for:
   - TLA+ specifications (the `tlaplus` language),
   - PlusCal code (the `pluscal` language),
   - TLA+ model definitions (the `tlaplus_cfg` language),
   - TLC output files (the `tlaplus_out` language), which is used for simple highlighting.
2. The main extension code that runs under the hood, handles user commands and reacts to various events.
3. The implementation of the Check Result View panel that visualizes TLC output and allows to analyze it easily.
4. The `tla2tools.jar` file from the [official TLA+ project](https://github.com/tlaplus/tlaplus). All the specification syntax verifications, PlusCal translations and TLC checks are actually performed by this Java library.

The extension also requires a Java Virtual Machine (JVM) to be installed. [More information](https://github.com/alygin/vscode-tlaplus/wiki/Installing-Java).

# Project Layout

## Manifest

The `package.json` file is both the [npm-package definition](https://docs.npmjs.com/creating-a-package-json-file) and the [extension manifest](https://code.visualstudio.com/api/get-started/extension-anatomy#extension-manifest). It defines the extension metadata, its dependencies, contributions to VS Code, build commands etc.

## Main Source Code

Most of the extension main code is located in the `src` directory. The only exception is the file `resources/check-result-view.js` which contains JavaScript code that empowers the Check Result View panel (more details below).

Names of files and subdirectories are usually self-descriptive. Here're the most interesting ones:

- `src/main.ts` &mdash; This is the starting point of the extension. It sets things up when the extension is loaded.
- `src/tla2tools.ts` &mdash; All the calls to `tla2tools.jar` go through methods from this file.
- `src/checkResultView.ts` &mdash; The main functions that are responsible for interaction between the main extension code and the Check Result View panel.
- `src/commands/` &mdash; This directory contains implementation of all the [VS Code commands](https://code.visualstudio.com/api/extension-guides/command) that the extension provides.
- `src/completions/` &mdash; The [code completion providers](https://code.visualstudio.com/api/references/vscode-api#CompletionItemProvider).
- `src/formatters/` &mdash; Classes that provide auto-formatting functionality.
- `src/model/` &mdash; The classes that describe model check results. Objects of these classes are used by the Check Result View panel.
- `src/parsers/` &mdash; Set of classes that parse output of the various TLA+ tools.
- `src/symbols/` &mdash; The classes that extract symbol information from files (constants, variables, operators etc.)

The files `resources/check-result-view.*` implement the Check Result View panel using [Webview API](https://code.visualstudio.com/api/extension-guides/webview).

## Tests

Tests are good!

They are placed in the `tests` directory. The files `runTest.ts` and `suite/index.ts` are used to setup the [Mocha testing framework](https://mochajs.org). And the other files and subdirectories use the same layout as the main source code.

## Other

There're some other useful stuff in the project:

- `.vscode/` &mdash; VS Code configuration files that make working with the project easier.
- `languages/` &mdash; Languages definition files.
- `tools/` &mdash; Additional artefacts that are used by the extesion.

# Source Code Style

Yeah, there are some rules about how the code should look, but they are not hard to follow.

[ESLint](https://eslint.org) is responsible for checking it as a part of building process. It uses the `.eslintrc.json` file as its config.

With the [ESLint extension](https://marketplace.visualstudio.com/items?itemName=dbaeumer.vscode-eslint) installed, VS Code will check your code automaticaly.

# Useful Resources

- [VS Code Extension API](https://code.visualstudio.com/api)
- [TypeScript documentation](https://www.typescriptlang.org/docs/home.html)
- [NodeJS documentation](https://nodejs.org/docs/latest-v8.x/api/)
- [TextMate 1.5 Grammars](https://macromates.com/manual/en/language_grammars)
- [Mocha Test Framework](https://mochajs.org)
- [GitHub &mdash; Collaborating](https://help.github.com/en/github/collaborating-with-issues-and-pull-requests)
