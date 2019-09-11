---- MODULE dependency ----
EXTENDS TLC, Integers

Thing == "thing"
Seven == 7
AddSeven(x) == x + Seven

THEOREM HmTheorem == \A x \in 1..2 : x # 8

====
