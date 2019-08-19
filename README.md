# TLA<sup>+</sup> for Visual Studio Code

[![Build Status](https://travis-ci.com/alygin/vscode-tlaplus.svg?token=xzkDSfrzMJUyGojFoW5V&branch=master)](https://travis-ci.com/alygin/vscode-tlaplus)

This extension adds support for the [TLA<sup>+</sup> formal specification language](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html) to VS Code. It also supports running the TLC model checker on TLA<sup>+</sup> specifications.

## Features

- TLA<sup>+</sup> and PlusCal syntax highlighting and code snippets.
- Running the PlusCal-to-TLA<sup>+</sup> translator and module parser.
- Running TLC model checker on TLA<sup>+</sup> specifications.
- Model checking process and result visualization.
- Powered by the [official TLA<sup>+</sup> toolbox](https://github.com/tlaplus/tlaplus).

<img src="https://raw.githubusercontent.com/alygin/vscode-tlaplus/master/resources/images/screencast.gif?token=AAQBAAUCHV5MRFM3AVUFS3K5LK5LO" width="800" height="auto">

## Requirements

In order to run various TLA<sup>+</sup> tools, you need Java 8 or higher installed. If it's not your default Java SDK, configure the proper Java Home path in the extension settings.

## Commands

The extension provides the following commands in the Command Palette:

- `TLA+: Parse module` for translating PlusCal to TLA<sup>+</sup> and checking syntax of the resulting specification.
- `TLA+: Check model` for running the TLC model checker on the TLA<sup>+</sup> specification.
- `TLA+: Visualize TLC output` for presenting model checking results.

## License

[MIT](LICENSE)
