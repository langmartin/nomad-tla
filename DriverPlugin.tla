-------------------------- MODULE CanaryPromotion --------------------------
EXTENDS Naturals, FiniteSets

CONSTANT
running = 1
stopped = 0
runState = {stopped, running}

VARIABLE driver, task

(*

docker/exec

embedded driver
1 per nomad agent
1 task + alloc at a time

external drivers pluggable as binaries
"plugin" as gprc, so the plugin runs as an external program

*)


FingerPrint == driver' \in runState /\ task' = task

DriverInit == driver' = FingerPrint /\ task' = task

DriverDestroy == driver' = stopped /\ task' = task

DriverNext == /\ FingerPrint
	      /\ driver' \in runState
	      /\ \/ (driver = running /\ task' = task)

(* we keep tasks running as long as they can, so if the driver is dead
   we can't run a new task but we'll keep the old ones going *)
   
		 \/ (driver = stopped /\ task' = task)

(* we use this verb a lot, it mirrors startup *)
Reattach == DriverInit






TaskStart == \/ driver = running /\ task = running
	     \/ driver = stopped /\ task = stopped

TaskWait == /\ task = running
	    /\ task \in runState /\ driver = running

TaskNext == \/ TaskWait
	    \/ TaskStart

Init == DriverInit
Next == /\ FingerPrint /\ TaskNext


=============================================================================
