// SYNTAX TEST "source.tlaplus" "tlaplus language grammar testcase for binary definitions"

---- MODULE Expect ----
// <---- comment.line 
//   ^^^^^^ keyword.other
//          ^^^^^^ entity.name.class

TODO == FALSE
// <--- support.type.primitive
//      ^^^^ support.constant.tlaplus

A == TODO \* B == C
// <- support.type.primitive
//   ^^^^ source.tlaplus
//         ^^^^^^^^ comment.line

A == TODO \* B = C
// <- support.type.primitive
//   ^^^^ source.tlaplus
//         ^^^^^^^^ comment.line

====
// <---- comment.line
