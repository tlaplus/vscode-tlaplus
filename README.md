# TLA<sup>+</sup> for Visual Studio Code

[![Build Status](https://img.shields.io/github/actions/workflow/status/tlaplus/vscode-tlaplus/ci.yml?branch=master)](https://github.com/tlaplus/vscode-tlaplus/actions?query=workflow%3ACI) [![Quality Gate](https://img.shields.io/sonar/quality_gate/alygin_vscode-tlaplus?server=https%3A%2F%2Fsonarcloud.io&style=flat-square)](https://sonarcloud.io/dashboard?id=alygin_vscode-tlaplus) [![VS Code extension version](https://img.shields.io/visual-studio-marketplace/i/alygin.vscode-tlaplus?color=blue&label=Stable%20Release&style=flat-square)](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus) [![VS Code extension version nightly](https://img.shields.io/visual-studio-marketplace/i/alygin.vscode-tlaplus-nightly?color=blue&label=Nightly%20Build&style=flat-square)](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus-nightly)

This extension adds support for the [TLA<sup>+</sup> formal specification language](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html) to VS Code. It also supports running the TLC model checker on TLA<sup>+</sup> specifications.

## Features

- TLA<sup>+</sup> and PlusCal syntax highlighting and code snippets.
- Running the PlusCal-to-TLA<sup>+</sup> translator and module parser.
- Running TLC model checker on TLA<sup>+</sup> specifications.
- Model checking process and result visualization.
- Evaluating constant expressions.
- Converting TLA<sup>+</sup> specifications to LaTeX and PDF documents.
- Code completion.
- Code on-type formatting.
- Powered by the [official TLA<sup>+</sup> tools](https://github.com/tlaplus/tlaplus).

<img src="https://raw.githubusercontent.com/tlaplus/vscode-tlaplus/master/resources/images/screencast.gif" width="800" height="auto">

## Documentation

[The project's Wiki](https://github.com/tlaplus/vscode-tlaplus/wiki) provides information on how to install, configure and use the extension.

* [How to Install](https://github.com/tlaplus/vscode-tlaplus/wiki/How-to-Install)
* [Getting Started](https://github.com/tlaplus/vscode-tlaplus/wiki/Getting-Started)
* [Settings](https://github.com/tlaplus/vscode-tlaplus/wiki/Settings)
* [Commands](https://github.com/tlaplus/vscode-tlaplus/wiki/Commands)
* [Setting up Environment](https://github.com/tlaplus/vscode-tlaplus/wiki/Setting-up-Environment)
* [Caveats](https://github.com/tlaplus/vscode-tlaplus/wiki/Caveats)
* [Troubleshooting](https://github.com/tlaplus/vscode-tlaplus/wiki/Troubleshooting)

## Contributing

All forms of contribution are highly welcome! Feel free to file bugs, propose improvements, ask questions, send other feedback.

If you decide to pitch in and write some code, this document will provide you with useful information: [CONTRIBUTING.md](CONTRIBUTING.md).

## TLA<sup>+</sup> Resources

If you're not familiar with TLA<sup>+</sup>, but want to get a grasp on it, the following list of resources is a good starting point:

* [TLA<sup>+</sup> Home Page](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html) on Leslie Lamport's website.
* [Introduction to TLA<sup>+</sup> and PlusCal](https://learntla.com) by Hillel Wayne.
* [TLA<sup>+</sup> in Practice and Theory](https://pron.github.io/posts/tlaplus_part1) by Ron Pressler.
* [A collection of TLA<sup>+</sup> specification examples](https://github.com/tlaplus/Examples) in the TLA<sup>+</sup> repository.

## License

[MIT](LICENSE)
