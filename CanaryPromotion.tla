-------------------------- MODULE CanaryPromotion --------------------------
EXTENDS Naturals, FiniteSets

VARIABLE old, new, count, command

TypeOk == /\ command \in {"promote", "rollback"}

Init == /\ old = 0
        /\ count = old + 1
        /\ new = 0
        /\ command = "promote"

RollingBack == command = "rollback"

Rollback == /\ RollingBack
            /\ old' = old + 1
            /\ new' = new - 1
            /\ count' = count
            /\ command' = "rollback"

RolledBack == /\ RollingBack
              /\ new = 0

Promoting == command = "promote"

Promote == /\ Promoting
           /\ old' = old - 1
           /\ new' = new + 1
           /\ count' = count

Promoted == /\ Promoting
            /\ old = 0


Live == Promoting \/ Promoted \/ RollingBack \/ RolledBack
Next == Promote \/ Rollback


=============================================================================
\* Modification History
\* Last modified Wed May 08 09:42:49 EDT 2019 by lang
\* Created Tue May 07 10:41:30 EDT 2019 by lang
