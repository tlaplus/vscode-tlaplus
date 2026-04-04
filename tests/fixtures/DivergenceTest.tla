---- MODULE DivergenceTest ----
(*
  Test file for PlusCal <> TLA+ divergence detection (issue #166).

  This file has valid checksums matching the PlusCal algorithm and its
  TLA+ translation. To test divergence detection:
  
  1. Open this file in VS Code with the TLA+ extension
  2. Add or remove a line inside the BEGIN/END TRANSLATION block
     (e.g. add "MyDef == TRUE" before the END TRANSLATION line)
  3. Run "TLA+: Parse Module" (Ctrl+Shift+P → TLA+: Parse Module)
  4. You should see a warning dialog about translation divergence
  5. Click "Cancel" to keep your changes, or "Translate Anyway" to overwrite
*)

(*
--algorithm DivAlgo
begin
  skip;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6690de28" /\ chksum(tla) = "af3d9146")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

====
