# Change Log

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
