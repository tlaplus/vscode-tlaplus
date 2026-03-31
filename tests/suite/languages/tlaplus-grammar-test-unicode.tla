// SYNTAX TEST "source.tlaplus" "Unicode operator grammar testcase"

---- MODULE UnicodeGrammarTest ----
// <---- comment.line

EXTENDS Naturals

VARIABLE x

\* ASCII backslash operators should get operator scopes
Init == x \in {1, 2, 3}
//        ^^^ keyword.operator.set.tlaplus

Next == \E y \in {1, 2, 3} : x' = y
//      ^^ keyword.operator.quantifier.tlaplus
//           ^^^ keyword.operator.set.tlaplus

Foo == x \land y
//       ^^^^^ keyword.operator.logic.tlaplus

Bar == x \leq y
//       ^^^^ keyword.operator.arithmetic.tlaplus

Baz == x \times y
//       ^^^^^^ keyword.operator.product.tlaplus

\* Unicode operators should get the SAME operator scopes
UnicodeIn == x ∈ S
//             ^ keyword.operator.set.tlaplus

UnicodeNotin == x ∉ S
//                ^ keyword.operator.set.tlaplus

UnicodeSubseteq == A ⊆ B
//                   ^ keyword.operator.set.tlaplus

UnicodeSubset == A ⊂ B
//                 ^ keyword.operator.set.tlaplus

UnicodeSupseteq == A ⊇ B
//                   ^ keyword.operator.set.tlaplus

UnicodeSupset == A ⊃ B
//                 ^ keyword.operator.set.tlaplus

UnicodeCup == A ∪ B
//              ^ keyword.operator.set.tlaplus

UnicodeCap == A ∩ B
//              ^ keyword.operator.set.tlaplus

UnicodeLnot == ¬ x
//             ^ keyword.operator.logic.tlaplus

UnicodeLand == x ∧ y
//               ^ keyword.operator.logic.tlaplus

UnicodeLor == x ∨ y
//              ^ keyword.operator.logic.tlaplus

UnicodeEquiv == x ≡ y
//                ^ keyword.operator.logic.tlaplus

UnicodeImplies == x ⇒ y
//                  ^ keyword.operator.logic.tlaplus

UnicodeLeq == x ≤ y
//              ^ keyword.operator.arithmetic.tlaplus

UnicodeGeq == x ≥ y
//              ^ keyword.operator.arithmetic.tlaplus

UnicodeLl == x ≪ y
//             ^ keyword.operator.arithmetic.tlaplus

UnicodeGg == x ≫ y
//             ^ keyword.operator.arithmetic.tlaplus

UnicodePrec == x ≺ y
//               ^ keyword.operator.arithmetic.tlaplus

UnicodeSucc == x ≻ y
//               ^ keyword.operator.arithmetic.tlaplus

UnicodeTimes == x × y
//                ^ keyword.operator.product.tlaplus

UnicodeForall == ∀ x \in S : x > 0
//               ^ keyword.operator.quantifier.tlaplus

UnicodeExists == ∃ x \in S : x > 0
//               ^ keyword.operator.quantifier.tlaplus

====
