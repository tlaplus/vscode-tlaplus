---- MODULE LibrarySpec ----
EXTENDS LibraryModule

VARIABLES val

Init == val = 0
Next == val' = val

====
