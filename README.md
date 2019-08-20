# <nobr>TLA<sup>+</sup></nobr> for Visual Studio Code

[![Build Status](https://travis-ci.com/alygin/vscode-tlaplus.svg?token=xzkDSfrzMJUyGojFoW5V&branch=master)](https://travis-ci.com/alygin/vscode-tlaplus)

This extension adds support for the [TLA<sup>+</sup> formal specification language](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html) to VS Code. It also supports running the TLC model checker on <nobr>TLA<sup>+</sup></nobr> specifications.

## Features

- TLA<sup>+</sup> and PlusCal syntax highlighting and code snippets.
- Running the PlusCal-to-<nobr>TLA<sup>+</sup></nobr> translator and module parser.
- Running TLC model checker on <nobr>TLA<sup>+</sup></nobr> specifications.
- Model checking process and result visualization.
- Powered by the [official TLA<sup>+</sup> toolbox](https://github.com/tlaplus/tlaplus).

<img src="https://raw.githubusercontent.com/alygin/vscode-tlaplus/master/resources/images/screencast.gif" width="800" height="auto">

## Requirements

In order to run various <nobr>TLA<sup>+</sup></nobr> tools, you need Java 8 or higher installed. If it's not your default Java SDK, configure the proper Java Home path in the extension settings.

## Commands

The extension provides the following commands in the Command Palette:

- `TLA+: Parse module` for translating PlusCal to <nobr>TLA<sup>+</sup></nobr> and checking syntax of the resulting specification.
- `TLA+: Check model` for running the TLC model checker on the <nobr>TLA<sup>+</sup></nobr> specification.
- `TLA+: Visualize TLC output` for presenting model checking results.

## Settings

- `Java: Home` allows to provide location of the JVM that the extension must use for running <nobr>TLA<sup>+</sup></nobr> tools.
- `Java: Options` allows to provide additional options that must be passed to a Java process when running <nobr>TLA<sup>+</sup></nobr> tools.

## License

[MIT](LICENSE)
