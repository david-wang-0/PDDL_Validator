Executing the validator
======================
1) Download and install [Isabelle/HOL](https://isabelle.in.tum.de)

 2) Install the Archive of Formal Proofs as indicated in [this
 page](https://www.isa-afp.org/using.shtml). We require version = Isabelle-2022,
 which, at the time of writing, is the current version.

 3) Open PDDL_Checker.thy, scroll to the bottom and wait until the file is nicely colored.
    This will output the generated code to: `PDDL-sema/PDDL_Checker_Exported.ML`

 4) Download and install [MLton](http://mlton.org/) compiler version `>= 20210117`.

 5) Build the generated sml code together with the pddl parser by running the
 following commands from the top directory
```
mlton -cc-opt -O3 -cc-opt -g0 pddl_validate_plan.mlb
```
Validating plans
================

 Given a pddl domain description file (e.g. examples/ged3-itt_no_invariants.pddl), a pddl
 instance (e.g. examples/d-1-2.pddl), and a plan file (e.g. examples/plan), from the top directory
 run:
```
./bin/validate_pddl_plan.sh examples/recharging_robots/recharging_robots_dom.pddl examples/recharging_robots/recharging_robots_prob.pddl examples/recharging_robots/recharging_robots_plan.plan    
```
 Note that the plan file has to have a plan in the IPC format, i.e. a list of
 action instances, each of which is as follows:

 ```
 (act_name arg1 arg2 ...)
 ```

 The validator will then give an output indicating the validation result.
