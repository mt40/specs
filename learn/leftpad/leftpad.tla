---- MODULE leftpad ----
EXTENDS TLC, Sequences, FiniteSets, Integers

SeqOf(char, count) == [1..count -> {char}]

(*--algorithm leftpad

variables
    CHARS = {"a", "b", "c"},
    input_str = <<"x", "x">>,
    pad_len \in 0..5,
    pad_char \in CHARS,
    output_str = <<>>;

begin
    if pad_len <= Len(input_str) then
        output_str := input_str;
    else
        output_str := SeqOf(pad_char, pad_len - Len(input_str));
        output_str := output_str \o input_str;
    end if;

    assert (
        pad_len > Len(input_str)
        /\ (\A i \in 1..(pad_len - Len(input_str)) : output_str[i] = pad_char)
    ) \/ (
        pad_len <= Len(input_str)
        /\ output_str = input_str
    );
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "478d0bb2" /\ chksum(tla) = "32005a2e")
VARIABLES CHARS, input_str, pad_len, pad_char, output_str, pc

vars == << CHARS, input_str, pad_len, pad_char, output_str, pc >>

Init == (* Global variables *)
        /\ CHARS = {"a", "b", "c"}
        /\ input_str = <<"x", "x">>
        /\ pad_len \in 0..5
        /\ pad_char \in CHARS
        /\ output_str = <<>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF pad_len <= Len(input_str)
               THEN /\ output_str' = input_str
                    /\ pc' = "Lbl_3"
               ELSE /\ output_str' = SeqOf(pad_char, pad_len - Len(input_str))
                    /\ pc' = "Lbl_2"
         /\ UNCHANGED << CHARS, input_str, pad_len, pad_char >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ output_str' = output_str \o input_str
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << CHARS, input_str, pad_len, pad_char >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ Assert(       (
                       pad_len > Len(input_str)
                       /\ (\A i \in 1..(pad_len - Len(input_str)) : output_str[i] = pad_char)
                   ) \/ (
                       pad_len <= Len(input_str)
                       /\ output_str = input_str
                   ), "Failure of assertion at line 23, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED << CHARS, input_str, pad_len, pad_char, output_str >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
