// SYNTAX TEST "source.tlaplus" "Extended TLA+ grammar test"

---- MODULE ExtendedGrammarTest ----

(* Test mathematical operators *)
TestSetOps == 
  /\ x \in S
//     ^^^ keyword.operator.set.tlaplus
  /\ y \notin T
//     ^^^^^^ keyword.operator.set.tlaplus
  /\ A \subseteq B
//     ^^^^^^^^^ keyword.operator.set.tlaplus
  /\ C \subset D
//     ^^^^^^^ keyword.operator.set.tlaplus
  /\ E \cup F = G
//     ^^^^ keyword.operator.set.tlaplus
  /\ H \cap I = J
//     ^^^^ keyword.operator.set.tlaplus
  /\ K \union L = M
//     ^^^^^^ keyword.operator.set.tlaplus
  /\ N \intersect O = P
//     ^^^^^^^^^^ keyword.operator.set.tlaplus

(* Test logic operators *)
TestLogicOps ==
  /\ P \land Q
//     ^^^^^ keyword.operator.logic.tlaplus
  /\ R \lor S
//     ^^^^ keyword.operator.logic.tlaplus
  /\ \lnot T
//   ^^^^^ keyword.operator.logic.tlaplus
  /\ U \equiv V
//     ^^^^^^ keyword.operator.logic.tlaplus
  /\ W \implies X
//     ^^^^^^^^ keyword.operator.logic.tlaplus

(* Test arithmetic operators *)
TestArithOps ==
  /\ a \leq b
//     ^^^^ keyword.operator.arithmetic.tlaplus
  /\ c \geq d
//     ^^^^ keyword.operator.arithmetic.tlaplus
  /\ e \neq f
//     ^^^^ keyword.operator.arithmetic.tlaplus
  /\ g \div h
//     ^^^^ keyword.operator.arithmetic.tlaplus

(* Test quantifiers *)
TestQuantifiers ==
  /\ \A x \in S : P(x)
//   ^^ keyword.operator.quantifier.tlaplus
  /\ \E y \in T : Q(y)
//   ^^ keyword.operator.quantifier.tlaplus
  /\ \forall z \in U : R(z)
//   ^^^^^^^ keyword.operator.quantifier.tlaplus
  /\ \exists w \in V : S(w)
//   ^^^^^^^ keyword.operator.quantifier.tlaplus

(* Test temporal operators *)
TestTemporalOps ==
  /\ []Invariant
//   ^^ keyword.operator.temporal.always.tlaplus
  /\ <>Eventually
//   ^^ keyword.operator.temporal.eventually.tlaplus
  /\ P ~> Q
//     ^^ keyword.operator.temporal.leadsto.tlaplus
  /\ [Next]_vars
//   ^ keyword.operator.temporal.action.tlaplus
  /\ <Next>_vars
//   ^ keyword.operator.temporal.action.tlaplus

(* Test sequences *)
TestSequences ==
  /\ seq = <<1, 2, 3>>
//         ^^ punctuation.definition.sequence.begin.tlaplus
//                  ^^ punctuation.definition.sequence.end.tlaplus
  /\ <<a, b, c>> \in Seq(S)
//   ^^ punctuation.definition.sequence.begin.tlaplus
//            ^^ punctuation.definition.sequence.end.tlaplus

(* Test set comprehension *)
TestSetComprehension ==
  /\ {x \in S : P(x)}
//   ^ punctuation.definition.set.begin.tlaplus
//            ^ keyword.operator.set.tlaplus
//                  ^ punctuation.definition.set.end.tlaplus

(* Test function construction *)
TestFunctionConstruction ==
  /\ [x \in Domain |-> f(x)]
//   ^ punctuation.definition.function.begin.tlaplus
//                 ^^^ keyword.operator.function.tlaplus
//                         ^ punctuation.definition.function.end.tlaplus

(* Test range operator *)
TestRange ==
  /\ 1..10
//    ^^ keyword.operator.range.tlaplus
  /\ a..b
//    ^^ keyword.operator.range.tlaplus

(* Test product operator *)
TestProduct ==
  /\ S \X T
//     ^^ keyword.operator.product.tlaplus
  /\ A \times B
//     ^^^^^^ keyword.operator.product.tlaplus

====