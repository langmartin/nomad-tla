-------------------------- MODULE Deployments --------------------------
EXTENDS Naturals, FiniteSets

\* Identifiers
CONSTANTS Jobs, Deployments

\* Sets of Deployments
VARIABLES watched, archive

\* Attributes of Deployments per Deployment (functions in the domain of Deployments)
VARIABLES job, status, type, count, healthy, time

StatusOk == {"running", "needs_promotion"}
StatusBad == {"failed"}
StatusAny == StatusOk \union StatusBad

DeploymentType == {"auto_promote", "auto_revert", "canary", "blue_green"}

\* Jobs == 1..3

\* Deployments ==
\*   \* the set of all possible deployments
\*   [type: DeploymentType, status: StatusAny, count: 1..3, healthy: 1..3, job: Jobs, time: 1..3]

TypeOk ==
  /\ watched \in Deployments
  /\ archive \in [Jobs -> Deployments]

Init ==
  /\ watched = Deployments
  /\ archive = [Jobs: {}]

-----------------------------------------------------------------------------

WatchedArchive(d) ==
  \* Stop watching the deployment, archive it for future rollbacks
  /\ archive[d.job]' = archive[d.job] \union {d}
  /\ watched' \ {d}

WatchedFail(d) ==
  \* If failed and drained, archive. Otherwise drain
  \/ /\ d.status = "failed"
     /\ d.healthy = 0
     /\ WatchedArchive(d)
  \/ /\ d.status' = "failed"
     /\ d.healthy' = d.healthy - 1
     /\ UNCHANGED <<archive>>

WatchedSucceed(d) ==
  /\ d.count = d.healthy
  /\ WatchedArchive(d)

WatchedTimeout(d) ==
  /\ d.time = 3
  /\ d.status' = "failed"

WatchedRun(d) ==
  /\ d.status \in StatusOk
  /\ \/ WatchedSucceed(d)
     \/ WatchedTimeout(d)
     \/ d.time' =




WatchedNext(d) ==
  \* advance the state of a watched deployment
  \/ WatchedFail(d)
  \/ WatchedRun(d)


Next == \A d \in watched: WatchedNext(d)

Spec == /\ Init /\ <>Next




RollingBack == status = "rollback"

Rollback == /\ RollingBack
            /\ old' = old + 1
            /\ new' = new - 1
            /\ count' = count
            /\ status' = "rollback"

RolledBack == /\ RollingBack
              /\ new = 0

Promoting == status = "promote"

Promote == /\ Promoting
           /\ old' = old - 1
           /\ new' = new + 1
           /\ count' = count

Promoted == /\ Promoting
            /\ old = 0


Live == Promoting \/ Promoted \/ RollingBack \/ RolledBack
Next == Promote \/ Rollback

=============================================================================
