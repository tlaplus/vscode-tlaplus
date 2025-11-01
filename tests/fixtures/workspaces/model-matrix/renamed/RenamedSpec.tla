---- MODULE RenamedSpec ----
EXTENDS Naturals

VARIABLES counter

Init == counter = 0
Next == counter' = counter + 1

====
