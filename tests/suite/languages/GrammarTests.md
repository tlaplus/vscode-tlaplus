# Grammar tests
Grammar tests test the grammars defined under the [languages](../../../languages) directory.

Current test coverage is:
- tlaplus-grammar.json

Grammar tests are defined under [tests/suite/languages](.)

A grammar test is a test file that includes annotation of the expected assigned scopes. One example is the [tlaplus-grammar-test.tla](tlaplus-grammar-test.tla).

For more information on how to write a test see [vscode-tmgrammar-test](thttps://github.com/PanAeon/vscode-tmgrammar-test).

## Run the tests
To run from the command line:
```
npm run test:tlaplus-grammar
```

To run from VS Code:
1. Open the project directory in VS Code.
2. Switch to the [Debug and Run](https://code.visualstudio.com/docs/editor/debugging) panel.
3. Select the "Run TLA Plus Grammar Tests" config.

## Adding tests
After adding a new test file for a grammar test:
- Update the npm command to include that test file in [package.json](../../../package.json).
- Update [launch.json](../../../.vscode/launch.json) to include an option to run the new test.