# TLA<sup>+</sup> for Visual Studio Code

[![Build Status](https://travis-ci.com/alygin/vscode-tlaplus.svg)](https://travis-ci.com/alygin/vscode-tlaplus) [![Quality Gate](https://img.shields.io/sonar/quality_gate/alygin_vscode-tlaplus?server=https%3A%2F%2Fsonarcloud.io)](https://sonarcloud.io/dashboard?id=alygin_vscode-tlaplus) [![VS Code extension version](https://img.shields.io/visual-studio-marketplace/v/alygin.vscode-tlaplus?color=blue&label=Visual%20Studio%20Marketplace&logo=visual-studio-code)](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus)

This extension adds support for the [TLA<sup>+</sup> formal specification language](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html) to VS Code. It also supports running the TLC model checker on TLA<sup>+</sup> specifications.

## Table of Contents
- [Features](#features)
- [Requirements](#requirements)
- [Commands](#commands)
- [Settings](#settings)
- [How to Start](#how-to-start)
- [Productivity Tips](#productivity-tips)
- [What to Read](#what-to-read)
- [License](#license)

## Features

- TLA<sup>+</sup> and PlusCal syntax highlighting and code snippets.
- Running the PlusCal-to-TLA<sup>+</sup> translator and module parser.
- Running TLC model checker on TLA<sup>+</sup> specifications.
- Model checking process and result visualization.
- Code on-type formatting.
- Powered by the [official TLA<sup>+</sup> tools](https://github.com/tlaplus/tlaplus).

<img src="https://raw.githubusercontent.com/alygin/vscode-tlaplus/master/resources/images/screencast.gif" width="800" height="auto">

## Requirements

In order to run various TLA<sup>+</sup> tools, you need Java 8 or higher (Java 11 is recommended) installed. If it's not your default Java SDK, configure the proper Java Home path in the extension settings.

## Commands

The extension provides the following commands in the Command Palette:

- `TLA+: Parse module` for translating PlusCal to TLA<sup>+</sup> and checking syntax of the resulting specification.
- `TLA+: Check model` for running the TLC model checker on the TLA<sup>+</sup> specification.
- `TLA+: Check model with non-default config...` for running the TLC model checker on the TLA<sup>+</sup> specification. Lets the user select a non-default model config file.
- `TLA+: Visualize TLC output` for presenting model checking results.

## Settings

- `Java: Home` allows to provide location of the JVM that the extension must use for running TLA<sup>+</sup> tools.
- `Java: Options` allows to provide additional options that must be passed to a Java process when running TLA<sup>+</sup> tools.
- `PlusCal: Options` allows to provide additional options to the PlusCal transpiler.
- `TLC Model Checker: Create Out Files` defines if TLC model checker output should be sent to a .out file.
- `TLC Model Checker: Options` allows to provide additional options to the TLC model checker.

## How to Start

The easiest way to get a working model is to create an empty PlusCal algorithm, translate it into a TLA<sup>+</sup> specification and run the TLC tool on it. Here's a step by step instruction:

Create a specification file. Let's name it `squares.tla`.

Make the file a TLA<sup>+</sup> module. To do it, start typing `module` and select the "Create new module (TLA+)" snippet from the drop-down list. The snippet will expand into module header and footer.

Use another snippet `pluscal` ("Create PlusCal block (TLA+)") to create an empty PlusCal algorithm. So far, we've got the following file:

```tla
---- MODULE squares ----
EXTENDS TLC

(*--algorithm squares

begin
    skip;
end algorithm; *)
====
```

Add some simple logic to it. For instance, let's make it check that squares of numbers from 1 to 10 do not exceed 100:

```tla
---- MODULE squares ----
EXTENDS TLC, Integers

(*--algorithm squares
variables
    x \in 1..10;

begin
    assert x ^ 2 <= 100;
end algorithm; *)
====
```

Run command `TLA+: Parse module`. It will translate the PlusCal algorithm to a TLA<sup>+</sup> specification (that will be added right into this file) and check it for errors.

We now have a simple specification that we can check by running the command `TLA+: Check model`. It will start the TLC tool on the currently open specification and display its progress and final result in a special panel.

One of the artefacts that the TLC command cerates when running on a `.tla` file with a PlusCal algorithm is a `.cfg` file that contains the model parameters. If you don't use PlusCal in your specification, the model configuration file will not be created automatically, but the extension will warn you about its absence and propose you to create it from a simple template.

You can find the full output of the TLC tool in a `.out` file that will be created near your specification. Should you need to visualize an output from a previous model checking, use the command `TLA+: Visualize TLC output` on a `.out` file.

## Productivity Tips

If you're going to use the extension for more than just syntax highlighting, a few tips may help to make your experience smoother:

* [Map keyboard shortcuts](https://code.visualstudio.com/docs/getstarted/keybindings) to the [extension commands](#commands). For instance, you might want to parse the current module by pressing `Ctrl+I` (`Command+I`) and to run the model checker by pressing `Ctrl+. Ctrl+.` (`Command+. Command+.`).
* Set the `editor.codeActionsOnSave` [setting](https://code.visualstudio.com/docs/getstarted/settings) for the `tlaplus` language to `{ "source": true }` and VSCode will run PlusCal transpiler and module checker automatically every time you save a .tla file.
* If you are using PlusCal, [edit settings](https://code.visualstudio.com/docs/getstarted/settings) to hide `.old` files from the Explorer panel. Those files are a by-product of the PlusCal transpiling process, and there's usually no need to deal with them directly. You'll need the `files.exclude` setting, and the pattern to add is `**/*.old`.
* [Take a look](https://github.com/alygin/vscode-tlaplus/blob/master/languages/pluscal-snippets.json) at the PlusCal code snippets the extension provides. They can save you a few keyboard strokes here and there.

## What to Read

If you're not familiar with TLA<sup>+</sup>, but want to get a grasp on it, the following list of resources is a good starting point:

* [TLA<sup>+</sup> Home Page](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html) on Leslie Lamport's website.
* [Introduction to TLA<sup>+</sup> and PlusCal](https://learntla.com) by Hillel Wayne.
* [TLA<sup>+</sup> in Practice and Theory](https://pron.github.io/posts/tlaplus_part1) by Ron Pressler.
* [A collection of TLA<sup>+</sup> specification examples](https://github.com/tlaplus/Examples) in the TLA<sup>+</sup> repository.

## License

[MIT](LICENSE)
