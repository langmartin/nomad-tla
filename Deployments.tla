-------------------------- MODULE Deployments --------------------------
EXTENDS Naturals, FiniteSets

\* Identifiers
CONSTANTS Jobs, Deployments

\* Sets of Deployments
VARIABLES watched, archive
GlobalVars == <<watched, archive>>

\* Attributes of Deployments per Deployment (functions in the domain of Deployments)
VARIABLES status, count, healthy, time,
	  canaries, healthy_canaries
DeploymentVars == <<status, count, healthy, time, canaries, healthy_canaries>>

StatusType == {"running", "needs_promotion", "failed"}

DeploymentType == {"canary", "blue_green"}
DeploymentOpts == {"auto_promote", "auto_revert"}

TypeOk ==
  /\ watched \in Deployments
  /\ archive \in Deployments

Init ==
  /\ watched = [id: Deployments, job: Jobs, type: DeploymentType, opts: DeploymentOpts]
  /\ archive = {}
  /\ status = [watched: {"running"}]
  /\ count = [watched: {3}]
  /\ healthy = [watched: {1}]
  /\ time = [watched: {0}]
  /\ canaries = [watched: {2}]
  /\ healthy_canaries = [watched: {0}]

-----------------------------------------------------------------------------

\* Stop watching the deployment, archive it for future rollbacks
WatchedArchive(d) ==
  /\ archive' = archive \union {d}
  /\ watched' \ {d}
  /\ UNCHANGED <<DeploymentVars>>

\* If failed and drained, archive. Otherwise drain
WatchedFail(d) ==
  \/ /\ status[d] = "failed"
     /\ healthy[d] = 0
     /\ WatchedArchive(d)
  \/ /\ status[d]' = "failed"
     /\ healthy[d]' = healthy[d] - 1
     /\ UNCHANGED <<archive, count, time>>

WatchedSucceed(d) ==
  /\ count[d] = healthy[d]
  /\ WatchedArchive(d)

WatchedNeedsPromote(d) ==
  /\ d.type = "
  /\ d \in watching
  /\ status[d] = "running"
  /\ canaries[d] = healthy_canaries[d]
  /\ needs[d]

WatchedTimeout(d) ==
  /\ time[d] = 3
  /\ status[d]' = "failed"
  /\ UNCHANGED <<count, GlobalVars>>

WatchedTick(d) ==
  /\ time[d]' = time[d] + 1
  /\ UNCHANGED <<GlobalVars, status, count, healthy>>

WatchedNext(d) ==
  \/ WatchedFail(d)
  \/ WatchedSucceed(d)
  \/ WatchedTimeout(d)
  \/ WatchedTick(d)

Next == \A d \in watched: WatchedNext(d)

Spec == /\ Init /\ Next

=============================================================================
