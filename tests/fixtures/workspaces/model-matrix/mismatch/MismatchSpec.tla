---- MODULE MismatchSpec ----
EXTENDS Naturals

VARIABLES flag

Init == flag = TRUE
Next == flag' = flag

====
