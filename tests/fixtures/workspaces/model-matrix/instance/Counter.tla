----- MODULE Counter ------

CONSTANT S
VARIABLE v

Spec == v = 0 /\ [][v' \in S]_v
=====
