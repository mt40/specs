---- MODULE sorting_machine ----
EXTENDS TLC, Sequences, FiniteSets, Integers

(*--algorithm sorting_machine
variable
    bins = [recycle |-> <<>>, trash |-> <<>>],
    capacity \in [recycle: 1..10, trash: 1..10],
    item_gen = [type: {"trash", "recycle"}, size: 1..6],
    items \in item_gen \X item_gen \X item_gen \X item_gen,
    cur; \* helper: current item

macro addItem(type, item) begin
    bins[type] := bins[type] \o <<item>>;
    capacity[type] := capacity[type] - item.size;
end macro;

begin
    while items # <<>> do
        cur := Head(items);

        if cur.type = "recycle" /\ cur.size <= capacity.recycle then
            addItem("recycle", cur);
        elsif cur.size <= capacity.trash then
            addItem("trash", cur);
        end if;

        items := Tail(items);
    end while;

    
    assert capacity.recycle >= 0 /\ capacity.trash >= 0;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "44ca57f0" /\ chksum(tla) = "ce342979")
CONSTANT defaultInitValue
VARIABLES bins, capacity, item_gen, items, cur, pc

vars == << bins, capacity, item_gen, items, cur, pc >>

Init == (* Global variables *)
        /\ bins = [recycle |-> <<>>, trash |-> <<>>]
        /\ capacity \in [recycle: 1..10, trash: 1..10]
        /\ item_gen = [type: {"trash", "recycle"}, size: 1..6]
        /\ items \in item_gen \X item_gen \X item_gen \X item_gen
        /\ cur = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items # <<>>
               THEN /\ cur' = Head(items)
                    /\ IF cur'.type = "recycle" /\ cur'.size <= capacity.recycle
                          THEN /\ bins' = [bins EXCEPT !["recycle"] = bins["recycle"] \o <<cur'>>]
                               /\ capacity' = [capacity EXCEPT !["recycle"] = capacity["recycle"] - cur'.size]
                          ELSE /\ IF cur'.size <= capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !["trash"] = bins["trash"] \o <<cur'>>]
                                          /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - cur'.size]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << bins, capacity >>
                    /\ items' = Tail(items)
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(capacity.recycle >= 0 /\ capacity.trash >= 0, 
                              "Failure of assertion at line 31, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << bins, capacity, items, cur >>
         /\ UNCHANGED item_gen

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
