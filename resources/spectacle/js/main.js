//
// TODO: See if all of this stuff can run fully locally.
//
// $ node main.js
//

const fs = require('fs');
const TreeSitter = require("./tree-sitter.js");
const Eval = require("./eval.js");
console.log("hello")

let parser = TreeSitter.init();
console.log(TreeSitter)


const url = `./tree-sitter-tlaplus.wasm`;
try {
    language = TreeSitter.Language.load(url);
} catch (e) {
    console.error(e);
    return;
}

// tree = null;
// parser.setLanguage(language);

console.log(Eval.jjjj())
let spec = new Eval.TLASpec("hello", "path");
// spec.parseSync()



// const Parser = require('tree-sitter');
//@ts-ignore
// const TlaPlus = require('@tlaplus/tree-sitter-tlaplus');

const wasmBuffer = fs.readFileSync(url);
WebAssembly.instantiate(wasmBuffer).then(wasmModule => {
  // Exported function live under instance.exports
  const { add } = wasmModule.instance.exports;
  const sum = add(5, 6);
  console.log(sum); // Outputs: 11
});

// const parser2 = new Parser();
// parser2.setLanguage("tlaplus");
// const source = `
// ---- MODULE Test ----
// f(x) == x
// ====
// `;
// const tree = parser.parse(source);
// console.log(tree.rootNode.toString());