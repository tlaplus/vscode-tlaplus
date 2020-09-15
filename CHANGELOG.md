# Change Log

## 1.5.1 &ndash; 16th September, 2020

### Enhancements

* Display more details about unsupported Java version.
* Support `CHECK_DEADLOCK` and `POSTCONDITION` keywords.

### Bug fixes

* Fix Java version parsing.
* Fix problem with quoted command line arguments.
* Fix Check Result View issue.

## 1.5.0 &ndash; 30th April, 2020

### Enhancements

* `Run last model check again` command which allows you to quickly run TLC again without switching to the spec or model file. The `Check again` button on the check visualization panel does the same.
* Upgrade TLA Tools to v2.15.
* Run the `Check model` command from the Explorer context menu on .tla and .cfg files.
* Display spec and model file names on the check visualization panel.
* Display errors when evaluating constant expressions.

## 1.4.0 &ndash; 3rd February, 2020

### Enhancements

* `Go to Definition` action implementation.
* Support custom class path in the `Java Options` setting.
* Switch between error traces when there are multiple of them.

### Bug fixes

* Fix warnings display.
* Correctly handle TLC results when the `-continue` option is used.
* Support new TLC message codes.
* Process TLC message codes with respect to severity levels.

## 1.3.2 &ndash; 14th January, 2020

### Bug fixes

* Fix Model Check Result view in VSCode Online.

## 1.3.0 &ndash; 5th January, 2020

### Enhancements

* Display variable values and copy them to clipboard from error trace.
* `TLC: Model Checker Options` setting now supports variables `${specName}` and `${modelName}`.
* New `TLC: Statistics Sharing` setting that allows to opt-in / opt-out sharing of TLC usage statistics ([more information](https://github.com/tlaplus/tlaplus/blob/master/tlatools/src/util/ExecutionStatisticsCollector.md)). Please, consider sharing.
* Allow workspace-level configuration.
* Various UI improvements.

### Bug fixes

* Fix some auto-indentation problems in C-style PlusCal algorithms.
* Fix operator overriding notification when using external modules.

## 1.2.0 &ndash; 20th October, 2019

### Enhancements

* Filter error-traces by variable names.
* "Go to definition" and "Peek definition" code actions.
* Display parsing warnings.
* Improve support for c-style PlusCal algorithms.
* Smarter code completion.
* Notify user about significant extension updates.

### Bug fixes

* Fix capturing of "bad indentation" SANY errors.

## 1.1.0 &ndash; 2nd October, 2019

### Enhancements

* Constant expression evaluation: new commands `TLA+: Evaluate selected expression` (also available in the context menu) and `TLA+: Evaluate expression...`.
* Integration with the [vscode-pdf extension](https://marketplace.visualstudio.com/items?itemName=tomoki1207.pdf) to quickly display generated PDFs.
* Don't create TLA<sup>+</sup>-related output channels until they are used.

### Bug fixes

* Display zero values correctly in the TLC output visualization panel.

## 1.0.0 &ndash; 15th September, 2019

### Enhancements

* Code completion in TLA<sup>+</sup> specifications and .cfg files.
* Export TLA<sup>+</sup> specifications to LaTeX and PDF documents.
* Symbols provider implementation (for the Outline view and "Go to symbol" command).
* Show / hide unmodified variables in error traces.
* Highlighting improvements.
* Drop the Preview badge.

## 0.7.1 &ndash; 8th September, 2019

### Enhancements

* Render source code links in error messages.
* Auto-indentation in .cfg files.
* Lots of syntax highlighting improvements.

## 0.6.0 &ndash; 5th September, 2019

### Enhancements

* New command `TLA+: Check model with non-default config...` allows the user to select a model config file for running model checking on a TLA<sup>+</sup> specification.
* New setting `TLC Model Checker: Create Out Files` allows the user to switch off sending the TLC output to a .out file.
* Support for running PlusCal transpiler and module parser automatically when a .tla file is saved.
* Output channels for TLC, PlusCal and SANY that allow the user to see raw output of these tools along with the full command line.

## 0.5.2 &ndash; 3rd September, 2019

### Bug fixes

* Fix default TLA<sup>+</sup> language indentation settings.
* Make snippets respect indentation settings.

## 0.5.1 &ndash; 1st September, 2019

### Enhancements

* Minor formatting improvements.

## 0.5.0 &ndash; 1st September, 2019

### Enhancements

* Code on-type formatting.
* Support custom TLC and PlusCal transpiler options (via settings).

### Bug fixes

* Fix parsing of PlusCal unrecoverable errors locations.

## 0.4.2 &ndash; 29th August, 2019

### Bug fixes

* Fix the "Stuttering" state parsing.
* Fix the "Back to state" state parsing.
* Recognize fair PlusCal algorithms.

## 0.4.1 &ndash; 25th August, 2019

### Enhancements

* Better PlusCal syntax highlighting.
* Better visualization of functions in error traces.
* Minor UI improvements.

### Bug fixes

* Fix the Stop button.
* Fix merged functions parsing.

## 0.4.0 &ndash; 24th August, 2019

### Enhancements

* Highlight actions with no executions in the coverage table.
* Minor UI improvements.

### Bug fixes

* Fix visualization when switching between an ongoing TLC process and a .out file.
* Fix coverage total/distinct numbers.

## 0.3.6 &ndash; 21st August, 2019

### Bug fixes

* Fix running TLA tools without custom Java options.
* Fix typo in the model checking execution report.

## 0.3.0 &ndash; 21st August, 2019

### Enhancements

* Jump from model checking results to definitions in source files.
* Syntax highlighting improvements.
* Allow to configure custom Java options.
* New snippets.
* Capture warnings in TLC output.
* Error traces parsing improvements.
* Improve model checking visualization.

### Bug fixes

* Fix TLC output parsing.
* Fix SANY output parsing.
* Fix parsing of TLA<sup>+</sup> tools output on Windows.

## 0.2.0 &ndash; 10th August, 2019

### Enhancements

* Mark changes in the variable values between states.
* Save TLC output to a .out file.
* Add `TLA+: Visualize TLC output` command (on .out files).
* Highlight message start/end markers in TLC output as comments.
* Check Java version before the first run.
* Check .tla and .cfg existence before running TLC.
* Allow the user to create a .cfg file from a template.
* Model checking visualization improvements.

## 0.1.0 &ndash; 4rd August, 2019

### Initial release

* TLA<sup>+</sup> and PlusCal syntax higlight.
* PlusCal-to-TLA<sup>+</sup> translation and parsing.
* Running TLC model checker.
* Display model check results.
