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

procedure do_something(param = "10") begin
    End:
        return;
end procedure;

process appender = "appender"
begin Push:
    await TRUE;
    when 1 = 1;
    Loop:
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
    Start:
    with foo = 10 do
        skip;
    end with;
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
    call do_something("something");
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e313c8def40ad1e3112011f0db802650
VARIABLES box, pc, stack

(* define statement *)
Nine == 9
AddSevenMulNine(x) == DEP!AddSeven(x) * Nine

VARIABLE param

vars == << box, pc, stack, param >>

ProcSet == {"appender"} \cup {"retriever"}

Init == (* Global variables *)
        /\ box = <<>>
        (* Procedure do_something *)
        /\ param = [ self \in ProcSet |-> "10"]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "appender" -> "Push"
                                        [] self = "retriever" -> "Start"]

End(self) == /\ pc[self] = "End"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ param' = [param EXCEPT ![self] = Head(stack[self]).param]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ box' = box

do_something(self) == End(self)

Push == /\ pc["appender"] = "Push"
        /\ TRUE
        /\ 1 = 1
        /\ pc' = [pc EXCEPT !["appender"] = "Loop"]
        /\ UNCHANGED << box, stack, param >>

Loop == /\ pc["appender"] = "Loop"
        /\ \/ /\ box' = Append(box, DEP!Thing)
           \/ /\ TRUE
              /\ box' = box
        /\ pc' = [pc EXCEPT !["appender"] = "Loop"]
        /\ UNCHANGED << stack, param >>

appender == Push \/ Loop

Start == /\ pc["retriever"] = "Start"
         /\ LET foo == 10 IN
              TRUE
         /\ pc' = [pc EXCEPT !["retriever"] = "Retrieve"]
         /\ UNCHANGED << box, stack, param >>

Retrieve == /\ pc["retriever"] = "Retrieve"
            /\ IF ~FALSE
                  THEN /\ IF Len(box) > 3
                             THEN /\ box' = Tail(Tail(box))
                             ELSE /\ IF Len(box) > 1
                                        THEN /\ box' = Tail(box)
                                        ELSE /\ TRUE
                                             /\ box' = box
                       /\ Assert(1 = 1, 
                                 "Failure of assertion at line 51, column 9.")
                       /\ pc' = [pc EXCEPT !["retriever"] = "Retrieve"]
                       /\ UNCHANGED << stack, param >>
                  ELSE /\ /\ param' = [param EXCEPT !["retriever"] = "something"]
                          /\ stack' = [stack EXCEPT !["retriever"] = << [ procedure |->  "do_something",
                                                                          pc        |->  "Done",
                                                                          param     |->  param["retriever"] ] >>
                                                                      \o stack["retriever"]]
                       /\ pc' = [pc EXCEPT !["retriever"] = "End"]
                       /\ box' = box

retriever == Start \/ Retrieve

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == appender \/ retriever
           \/ (\E self \in ProcSet: do_something(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-99759f1c5215f35e6e3d7f37c9798c1a
====
