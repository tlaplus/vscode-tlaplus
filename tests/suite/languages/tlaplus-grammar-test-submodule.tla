// SYNTAX TEST "source.tlaplus" "tlaplus language grammar testcase"

---- MODULE SubmoduleTest ----
// <---- comment.line 
//   ^^^^^^ keyword.other
//          ^^^^^^^^^^^^^ entity.name.class
---- MODULE InnerModule1 ----
// <---- comment.line
//   ^^^^^^ keyword.other
//          ^^^^^^^^^^^^ entity.name.class

Op1 == FALSE
//<-- support.type.primitive
//     ^^^^^ support.constant.tlaplus

====
// <---- comment.line

---- MODULE InnerModule2 ----
// <---- comment.line
//   ^^^^^^ keyword.other
//          ^^^^^^^^^^^^ entity.name.class

Op2 == FALSE
//<-- support.type.primitive
//     ^^^^^ support.constant.tlaplus


====
// <---- comment.line

Op == FALSE
//<-- support.type.primitive
//    ^^^^^ support.constant.tlaplus

====
// <---- comment.line
