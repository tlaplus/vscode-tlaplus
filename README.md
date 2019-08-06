# TLA<sup>+</sup> for Visual Studio Code

This extension adds support for the [TLA<sup>+</sup> formal specification language](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html) to VS Code. It also supports running the TLC model checker on TLA<sup>+</sup> specifications.

## Features

- TLA<sup>+</sup> and PlusCal syntax highlighting and code snippets.
- Running the PlusCal-to-TLA<sup>+</sup> translator and module parser.
- Running TLC model checker on TLA<sup>+</sup> specifications.
- Powered by the [official TLA<sup>+</sup> toolbox](https://github.com/tlaplus/tlaplus).

## Requirements

In order to run various TLA<sup>+</sup> tools, you need Java 8 or higher installed. If it's not your default Java SDK, configure the proper Java Home path in the extension settings.

## Commands

The extension provides the following commands in the Command Palette (only available when working with a .tla-file):

- `TLA+: Parse module` for translating PlusCal to TLA<sup>+</sup> and checking syntax of the resulting specification.
- `TLA+: Check model` for running the TLC model checker on the TLA<sup>+</sup> specification.

## License

[MIT](LICENSE)
