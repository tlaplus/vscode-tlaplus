---- MODULE squares ----
EXTENDS Naturals, TLC

(* --algorithm squares
variables i = 0;
begin
Lbl_1:
    while i < 10 do
        assert i * i <= 100;
        i := i + 1;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ee399873" /\ chksum(tla) = "53668846")
VARIABLES pc, i

vars == << pc, i >>

Init == (* Global variables *)
        /\ i = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i < 10
               THEN /\ Assert(i * i <= 100, 
                              "Failure of assertion at line 9, column 9.")
                    /\ i' = i + 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ i' = i

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <> (pc = "Done")

\* END TRANSLATION 

====
