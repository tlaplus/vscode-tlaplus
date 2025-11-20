function tlaplusMode(obj, modeConfig){
    console.log(obj);
    console.log(modeConfig);

    var external = {
        startState: function(basecolumn) {
          return {
            tokenize: null,
            scope: {offset:basecolumn || 0, type:"coffee", prev: null, align: false},
            prop: false,
            dedent: 0
          };
        },
    
        token: function(stream, state) {
        // console.log(stream);
        stream.sol();
        stream.next();
        //   var fillAlign = state.scope.align === null && state.scope;
        //   if (fillAlign && stream.sol()) fillAlign.align = false;
    
        //   var style = tokenLexer(stream, state);
        //   if (style && style != "comment") {
        //     if (fillAlign) fillAlign.align = true;
        //     state.prop = style == "punctuation" && stream.current() == "."
        //   }

         // TODO: Customize this to proper coloring.
         return "none";
         return "keyword";
         return "error";
         return "variable";
    
          return style;
        },
    
        indent: function(state, text) {
          if (state.tokenize != tokenBase) return 0;
          var scope = state.scope;
          var closer = text && "])}".indexOf(text.charAt(0)) > -1;
          if (closer) while (scope.type == "coffee" && scope.prev) scope = scope.prev;
          var closes = closer && scope.type === text.charAt(0);
          if (scope.align)
            return scope.alignOffset - (closes ? 1 : 0);
          else
            return (closes ? scope.prev : scope).offset;
        },
    
        lineComment: "\\*",
        fold: "indent"
      };
    return external;
}

// CodeMirror.defineMode("tlaplus", tlaplusMode);


CodeMirror.defineSimpleMode("tlaplus", {
    // The start state contains the rules that are initially used
    start: [
      // The regex matches the token, the token property contains the type
      {regex: /"(?:[^\\]|\\.)*?(?:"|$)/, token: "string"},
      // You can match multiple tokens at once. Note that the captured
      // groups must span the whole string in this case
      {regex: /(function)(\s+)([a-z$][\w$]*)/,
       token: ["keyword", null, "variable-2"]},
      // Rules are matched in the order in which they appear, so there is
      // no ambiguity between this one and the one above
      {regex: /(?:VARIABLE|CONSTANT|CONSTANTS|EXTENDS|MODULE)\b/,
       token: "keyword"},
      {regex: /\\A|\\E|\\in|<<|>>/, token: "keyword"},
      {regex: /0x[a-f\d]+|[-+]?(?:\.\d+|\d+\.?\d*)(?:e[-+]?\d+)?/i,
       token: "number"},
      {regex: /\\\*.*/, token: "comment"},
    //   {regex: /\/(?:[^\\]|\\.)*?\//, token: "variable-3"},
      // A next property will cause the mode to move to a different state
      {regex: /\(\*/, token: "comment", next: "comment"},
    //   {regex: /[-+\/*=<>!]+/, token: "operator"},
      // indent and dedent properties guide autoindentation
    //   {regex: /[\{\[\(]/, indent: true},
    //   {regex: /[\}\]\)]/, dedent: true},
    //   {regex: /[a-z$][\w$]*/, token: "variable"},
      // You can embed other modes with the mode property. This rule
      // causes all code between << and >> to be highlighted with the XML
      // mode.
      {regex: /<</, token: "meta", mode: {spec: "xml", end: />>/}}
    ],
    // The multi-line comment state.
    comment: [
      {regex: /.*?\*\)/, token: "comment", next: "start"},
      {regex: /.*/, token: "comment"}
    ],
    // The meta property contains global information about the mode. It
    // can contain properties like lineComment, which are supported by
    // all modes, and also directives like dontIndentStates, which are
    // specific to simple modes.
    meta: {
      dontIndentStates: ["comment"],
      lineComment: "\\*"
    }
  });