\*The bomb is in a briefcase with a precise electronic scale.
\*McClane and Zeus have a 5-gallon jug and a 3-gallon jug.
\*They are standing next to a fountain where they can take as much water as they want.
\*They have to put one of the jugs on the scale with exactly 4 gallons of
\*water in it, or the bomb will detonate.
\*How do you get exactly 4 gallons of water into one of the jugs?

---- MODULE diehard ----
EXTENDS Integers
VARIABLES small, big

\*invariants
TypeOk == /\ small \in 0..3
          /\ big \in 0..5
FourLiter == big /= 4

\*operations
FillSmall == small' = 3 /\ big' = big
FillBig == big' = 5 /\ small' = small
EmptySmall == small' = 0 /\ big' = big
EmptyBig == big' = 0 /\ small' = small
SmallToBig ==
    IF small + big =< 5
    THEN small' = 0 /\ big' = small + big
    ELSE /\ big' = 5
        /\ small' = small - (5 - big)
BigToSmall ==
    IF small + big =< 3
    THEN big' = 0 /\ small' = small + big
    ELSE /\ small' = 3
        /\ big' = big - (3 - small)

\*state transition
Init == /\ big = 0
        /\ small = 0
Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

====