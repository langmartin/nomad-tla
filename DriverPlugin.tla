-------------------------- MODULE DriverPlugin --------------------------
EXTENDS FiniteSets

VARIABLE driver, task, runState

TypeOk == /\ runState = {"running", "stopped"}
          /\ driver \in runState
          /\ task \in runState

(*

docker/exec

embedded driver
1 per nomad agent
1 task + alloc at a time

external drivers pluggable as binaries
"plugin" as gprc, so the plugin runs as an external program

*)

------------------------------------------------------------------------

FingerPrint == driver' \in runState /\ task' = task

(* we keep tasks running as long as they can, so if the driver is dead
   we can't run a new task but we'll keep the old ones going *)

DriverStop == /\ driver = "stopped" /\ task' = task

Reattach == /\ task = "running" /\ driver' = "running"

TaskStart == /\ driver = "running" /\ task' = "running"

------------------------------------------------------------------------

Init == /\ TypeOk
        /\ driver = "running"
        /\ task = "stopped"

Next == /\ FingerPrint
        /\ \/ DriverStop
           \/ Reattach
           \/ TaskStart

=============================================================================
