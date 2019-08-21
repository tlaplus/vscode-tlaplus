# TLA<sup>+</sup> for Visual Studio Code

[![Build Status](https://travis-ci.com/alygin/vscode-tlaplus.svg)](https://travis-ci.com/alygin/vscode-tlaplus)

This extension adds support for the [TLA<sup>+</sup> formal specification language](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html) to VS Code. It also supports running the TLC model checker on TLA<sup>+</sup> specifications.

## Features

- TLA<sup>+</sup> and PlusCal syntax highlighting and code snippets.
- Running the PlusCal-to-TLA<sup>+</sup> translator and module parser.
- Running TLC model checker on TLA<sup>+</sup> specifications.
- Model checking process and result visualization.
- Powered by the [official TLA<sup>+</sup> tools](https://github.com/tlaplus/tlaplus).

<img src="https://raw.githubusercontent.com/alygin/vscode-tlaplus/master/resources/images/screencast.gif" width="800" height="auto">

## Requirements

In order to run various TLA<sup>+</sup> tools, you need Java 8 or higher installed. If it's not your default Java SDK, configure the proper Java Home path in the extension settings.

## Commands

The extension provides the following commands in the Command Palette:

- `TLA+: Parse module` for translating PlusCal to TLA<sup>+</sup> and checking syntax of the resulting specification.
- `TLA+: Check model` for running the TLC model checker on the TLA<sup>+</sup> specification.
- `TLA+: Visualize TLC output` for presenting model checking results.

## Settings

- `Java: Home` allows to provide location of the JVM that the extension must use for running TLA<sup>+</sup> tools.
- `Java: Options` allows to provide additional options that must be passed to a Java process when running TLA<sup>+</sup> tools.

## How to start

The easiest way to get a working model is to create an empy PlusCal algorithm, translate it into a TLA<sup>+</sup> specification and run the TLC tool on it. Here's a step by step instruction:

Create a specification file. Let's name it `squares.tla`.

Make the file a TLA<sup>+</sup> module. To do it, start typing `module` and select the "Create new module (TLA+)" snippet from the drop down list. The snippet will expand into module header and footer.

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

Run command `TLA+: Parse module`. It will transpile the PlusCal algorithm to TLA<sup>+</sup> specification (that will be added right into this file) and check it for errors.

We now have a simple specification that we can check by running the command `TLA+: Check model`. The command will start the TLC tool on the currently open specification and display its progress and final result in a special panel.

One of the artifacts that the TLC command cerates when running on a `.tla` file with a PlusCal algorithm is a `.cfg` file that contains the model parameters. If you don't use PlusCal in your specification, the model configuration file will not be created automatically, but the extension will warn you about its absense and propose you to create it from a simple template.

You can find the full output of the TLC tool in a `.out` file that will be created near your specification. Should you need to visualize an output from a previous model checking, use the command `TLA+: Visualize TLC output` on a `.out` file.

## What to read

* [TLA<sup>+</sup> Home Page](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html) on Leslie Lamport's website.
* [Introduction to TLA<sup>+</sup> and PlusCal](https://learntla.com) by Hillel Wayne.
* [TLA<sup>+</sup> in Practice and Theory](https://pron.github.io/posts/tlaplus_part1) by Ron Pressler.
* [A collection of TLA<sup>+</sup> specification examples](https://github.com/tlaplus/Examples) in the TLA<sup>+</sup> repository.

## License

[MIT](LICENSE)
