# PDDL4J
This repo contains 2 IPC2023 entries.\
Planner functionality is briefly described in the corresponding papers. Papers are available in the repo.

## OptiPlan
CSP-based Partial Order planner

Usage:
> optiplan.jar csp po $DOMAINFILE $PROBLEMFILE

To execute via apptainer:
> sudo apptainer build OptiPlan.sif OptiPlan.def\
> apptainer run OptiPlan.sif [hddl domain] [hddl problem]

## LiftedTreePath
SMT-based Total Order planner

Usage:
>
