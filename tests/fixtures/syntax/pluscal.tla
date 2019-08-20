---- MODULE pluscal ----
EXTENDS TLC, Integers, Sequences
DEP == INSTANCE dependency

(*--algorithm pluscal
variables box = <<>>;

define
    Nine == 9
    AddSevenMulNine(x) == DEP!AddSeven(x) * Nine
end define;

macro do_nothing(param) begin
    skip;
end macro;

process appender = "appender"
begin Push:
    while TRUE do
        either
            box := Append(box, DEP!Thing);
        or
            skip;
        end either;
    end while;
end process;

process retriever = "retriever"
begin
    Retrieve:
    while ~FALSE do
        if Len(box) > 3 then
            box := Tail(Tail(box))
        elsif Len(box) > 1 then
            box := Tail(box);
        else
            skip;
        end if;
        assert 1 = 1;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES box, pc

(* define statement *)
Nine == 9
AddSevenMulNine(x) == DEP!AddSeven(x) * Nine


vars == << box, pc >>

ProcSet == {"appender"} \cup {"retriever"}

Init == (* Global variables *)
        /\ box = <<>>
        /\ pc = [self \in ProcSet |-> CASE self = "appender" -> "Push"
                                        [] self = "retriever" -> "Retrieve"]

Push == /\ pc["appender"] = "Push"
        /\ \/ /\ box' = Append(box, DEP!Thing)
           \/ /\ TRUE
              /\ box' = box
        /\ pc' = [pc EXCEPT !["appender"] = "Push"]

appender == Push

Retrieve == /\ pc["retriever"] = "Retrieve"
            /\ IF ~FALSE
                  THEN /\ IF Len(box) > 3
                             THEN /\ box' = Tail(Tail(box))
                             ELSE /\ IF Len(box) > 1
                                        THEN /\ box' = Tail(box)
                                        ELSE /\ TRUE
                                             /\ box' = box
                       /\ Assert(1 = 1, 
                                 "Failure of assertion at line 39, column 9.")
                       /\ pc' = [pc EXCEPT !["retriever"] = "Retrieve"]
                  ELSE /\ pc' = [pc EXCEPT !["retriever"] = "Done"]
                       /\ box' = box

retriever == Retrieve

Next == appender \/ retriever

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
====
