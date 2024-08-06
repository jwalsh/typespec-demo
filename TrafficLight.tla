---- MODULE TrafficLight ----
EXTENDS Integers

VARIABLES light

TypeOK == light \in {"red", "yellow", "green"}

Init == light = "red"

Next == 
    \/ /\ light = "red"
       /\ light' = "green"
    \/ /\ light = "green"
       /\ light' = "yellow"
    \/ /\ light = "yellow"
       /\ light' = "red"

Spec == Init /\ [][Next]_light

====
