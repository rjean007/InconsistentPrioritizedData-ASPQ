# Using ASP(Q) to Handle Inconsistent Prioritized Data

We describe here how to use the implementation of the algorithms presented in the submitted at KR 2026 paper. 

The proposed implementation is built on top of the clingo and Casper systems that must be correctly installed.
The clingo system can be installed as python package via pip (i.e., pip install clingo).
The source code of Casper system is available in the Casper folder (see installation instruction in Casper README).

python3.11 or later is required.

Benchmark data files can be found on the zenodo repository https://doi.org/10.5281/zenodo.19705686.

## Description

Use main.py to evaluate query potential answers under different semantics

### Input

"--conflicts CONFLICTS"  allows to specify the path to the conflict file.

Type of conflict considered (either binary or non binary): "--conf_type {non_binary,binary}"


"--answers ANSWERS"   allows to specify the path to the potential answers file. (Optional for the computation of the attack relation and the grounded extension)



Then one can select one of the following tasks:

#### Attack relation generation

To generate the attack relation of a given conflict graph add the argument "--generate-attacks".

#### Grounded extension generation

To generate the grounded extension of a given conflict graph add the argument "--generate-extension".

#### Query answering under prioritized repair based semantics

Type of repair considered: "--repairs {pareto,completion,global,trivial_grounded}"
                        
Semantics considered: "--semantics {BRAVE,AR}"

Type of localization: "--reach {none,weak,strong}"


### Usage Examples

Most of the reasoning task that can be carried out with our implementation need to precompute "attacks" relation.

This can be done with the following command:
```
python3 main.py --generate-attacks --conf_type binary --conflicts example/conflicts/u1c1_conflictGraph_prio_non_score_p08.lp
```

Once the attack relation has been computed for a given knowledge base, the following tasks can be carried out:




#### Computing grounded extension for u1c1 under non_score structure
```
python3 main.py --generate-extension --conf_type binary --conflicts example/conflicts/u1c1_conflictGraph_prio_non_score_p08.lp
```

#### Computing trivial and grounded potential answers for the query q11 for u1c1 under non_score structure
First generate the grounded extension as in the previous example and then execute the following command
```
python3 main.py --repairs trivial_grounded --conf_type binary --conflicts example/conflicts/u1c1_conflictGraph_prio_non_score_p08.lp --answers example/trivial_grounded/u1c1/potAns/q11_potAns.lp
```

#### Checking whether potential answer "350990" for the query q11 on u1c1 under non_score structure is global AR  
```
python3 main.py --repairs global --semantics AR --conf_type binary --conflicts example/conflicts/u1c1_conflictGraph_prio_non_score_p08.lp --answers example/other_repairs/u1c1_conflictGraph_prio_non_score_p08.lp-q11/pot_ans_350990.lp
```
                  
