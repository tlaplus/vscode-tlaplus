This file is for checking syntax higlighting for the TLA+ language.

---- MODULE tlaplus ----
EXTENDS TLC, Integers, Sequences
DEP == INSTANCE dependency

CONSTANTS Foo, Bar
CONSTANT FooBar

ASSUME Foo > Bar

\* Line comment
(* - block comment
   - still block comment
*)
(* block comment in one line *)
\* below are separation lines which are also comments
    -------------------------------------------
----
--------------

\* Constants
Baz == 1003
FizzBuzz == {"1", "2", "Fizz", "4", "Buzz", "Fizz", "7", "8", "Fizz", "Buzz", "11", "Fizz", "13", "14", "Fizz Buzz", "16"}
Bools == { TRUE, FALSE }
Range == -5..50
OneToFive == << 1, 2, 3, 4, 5 >>
Three == OneToFive[3]

\* Operators, lambdas
SeqMax(seq) == CHOOSE x \in seq: \A y \in seq: x >= y
CallAndAddSeven(op(_, _), p1, p2) ==
    LET CallResult == op(p1, p2)
    IN DEP!AddSeven(CallResult)

PlusFive == CallAndAddSeven(LAMBDA x, y: x + y, 4, 5)

\* Functions
Not[param \in BOOLEAN] == ~param
SimpleFunc == (10 :> "ten")
MergeFuncsShort(f, g) == f @@ g
MergeFuncsLong(f, g) == [
    x \in DOMAIN f \union DOMAIN g |->
        IF x \in DOMAIN f THEN f[x] ELSE g[x]
]

\* Operators redefinition
Left !! Right == Left
Left ## Right == Left
Left $ Right == Left
Left $$ Right == Right
Left %% Right == Left
Left & Right == Left
Left && Right == Left
Left (+) Right == Left
Left (-) Right == Left
Left (.) Right == Left
Left (/) Right == Left
Left (\X) Right == Left
Left ++ Right == Right
Left -- Right == Right
Left -| Right == Right
Left ... Right == Right
Left / Right == Right
Left // Right == Right
Left ::= Right == Right
Left := Right == Right
Left <: Right == Right
Left =| Right == Right
Left ?? Right == Right
Left ^^ Right == Right
Left | Right == Right
Left |- Right == Left
Left \gg Right == Left
Left \approx Right == Left

\* Postfix operators redefinition
Par^+ == 10
Par^* == 10
Par^# == 10

VARIABLES foo, bar, pc

vars == << foo, bar, pc >>

Init == (* Global variables *)
    /\ foo = TRUE
    /\ bar = 10
    /\ pc = "Step_1"

Step_1 == /\ pc = "Step_1"
          /\ IF bar > 5 /\ bar < 15
             THEN /\ IF foo /\ Len(<<>>) = 0
                     THEN /\ bar' = bar - 1
                          /\ foo' = FALSE
                     ELSE /\ bar' = bar + 1
                          /\ UNCHANGED << foo >>
                  /\ UNCHANGED << pc >>
             ELSE
                  /\ pc' = "Done"
                  /\ UNCHANGED << foo, bar >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == Step_1 \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

====

This text is ignored.
