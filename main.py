import clingo,os,subprocess
import argparse,sys

PARETO = "pareto"
COMPLETION = "completion"
GLOBAL = "global"
TRIVIAL_GROUNDED = "trivial_grounded"

NOT = "none"
WEAK = "weak"
STRONG = "strong"


BRAVE = "BRAVE"
AR = "AR"

BIN = "binary"
NON_BIN = "non_binary"

SOLVER_HOME=None

def parse_args():
    parser = argparse.ArgumentParser(
        description="Process conflicts and potential answers with a given solving modality."
    )

    parser.add_argument(
        "--conflicts",
        required=True,
        type=str,
        help="Path to the conflict file"
    )

    parser.add_argument(
        "--answers",
        type=str,
        help="Path to the potential answers file"
    )

    parser.add_argument(
        "--repairs",
        type=str,
        choices=[PARETO, COMPLETION, GLOBAL, TRIVIAL_GROUNDED],
        default=TRIVIAL_GROUNDED,
        help="Type of repairs"
    )

    parser.add_argument(
        "--semantics",
        type=str,
        choices=[BRAVE, AR],
        default=BRAVE,
        help="Select the type of semantics"
    )

    parser.add_argument(
        "--conf_type",
        type=str,
        choices=[NON_BIN, BIN],
        default=NON_BIN,
        help="Select the type of conflict (either binary or non binary)"
    )

    parser.add_argument(
        "--reach",
        type=str,
        choices=[NOT, WEAK, STRONG],
        default=STRONG,
        help="Select the type of reachability notion considered"
    )

    parser.add_argument(
        "--generate-extension",
        action="store_true",
        default=False,
        help="Enable generation of grounded extension"
    )

    parser.add_argument(
        "--generate-attacks",
        action="store_true",
        default=False,
        help="Enable generation of the attack relation"
    )

    return parser.parse_args()



def compute_attacks(conflicts_file, conf_type):

    conf_name = os.path.basename(conflicts_file)
    ATTACKS_FILE=f"{SOLVER_HOME}/{os.path.splitext(conf_name)[0]}_attacks_{conf_type}.lp"
    ctl = clingo.Control()
    ctl.add("base",[],attacks)
    ctl.load(conflicts_file)
    ctl.ground([("base", [])])

    with ctl.solve(yield_=True) as handle:
        for model in handle:
            with open(ATTACKS_FILE,"w") as a:
                        for atom in model.symbols(shown=True):
                            if atom.type == clingo.SymbolType.Function and atom.name == "attacks":
                                print(f"{atom}.",file=a)
    return False

def solver_pareto(conflicts_file,pans_file,isBrave, reach_type, conf_type):
    conf_name = os.path.basename(conflicts_file)
    CONSTRAINT_FILE=f'{SOLVER_HOME}/semantics/specific_{conf_type}_encodings/pareto/{BRAVE if isBrave else AR}_pareto.asp'
    ATTACKS_FILE=f"{SOLVER_HOME}/{os.path.splitext(conf_name)[0]}_attacks_{conf_type}.lp"
    REACH_FILE = f'{SOLVER_HOME}/semantics/specific_{conf_type}_encodings/pareto/reachable_{reach_type}.asp' if conf_type == "non_binary" else ""
    ENCODING_FILE=f"{SOLVER_HOME}/semantics/specific_{conf_type}_encodings/pareto/pareto.asp"

    result = subprocess.getoutput(f"clingo -V0  {ENCODING_FILE} {REACH_FILE} {ATTACKS_FILE} {CONSTRAINT_FILE} {conflicts_file} {pans_file}")
    ans = result.split("\n")
    ans = ans[0] if len(ans) == 1 else ans[-1]
    if ans == "UNSATISFIABLE":
        return True if not isBrave else False
    if ans == "SATISFIABLE":
        return False if not isBrave else True 
    assert False

def solver_completion(conflicts_file,pans_file,isBrave, reach_type, conf_type):
    
    conf_name = os.path.basename(conflicts_file)
    CONSTRAINT_FILE=f'{SOLVER_HOME}/semantics/specific_{conf_type}_encodings/completion/{BRAVE if isBrave else AR}_completion.asp'
    ATTACKS_FILE=f"{SOLVER_HOME}/{os.path.splitext(conf_name)[0]}_attacks_{conf_type}.lp"
    REACH_FILE = f'{SOLVER_HOME}/semantics/specific_{conf_type}_encodings/completion/reachable_{reach_type}.asp' if conf_type == "non_binary" else ""
    ENCODING_FILE=f"{SOLVER_HOME}/semantics/specific_{conf_type}_encodings/completion/completion.asp"
    result = subprocess.getoutput(f"clingo -V0 {ENCODING_FILE} {REACH_FILE} {ATTACKS_FILE} {CONSTRAINT_FILE} {conflicts_file} {pans_file}")
    ans = result.split("\n")
    ans = ans[0] if len(ans) == 1 else ans[1]

    if ans == "UNSATISFIABLE":
        return True if not isBrave else False
    if ans == "SATISFIABLE":
        return False if not isBrave else True 
    assert False 

def compute_grounded_extention(conflicts_file, conf_type):
    conf_name = os.path.basename(conflicts_file)
    GROUNDED_FILE=f"{SOLVER_HOME}/{conf_name}_{conf_type}_grounded_ext.lp"
    TRIVIAL_EXTENSION=f"{SOLVER_HOME}/{conf_name}_{conf_type}_trivial_ext.lp"
    ATTACKS_FILE=f"{SOLVER_HOME}/{os.path.splitext(conf_name)[0]}_attacks_{conf_type}.lp"
    
    ctl = clingo.Control()
    program_base = """
        unsafe(Id, 0) :- attacks(C, Id). 
        safe(Id, 0) :- inConf(C, Id), not unsafe(Id, 0). 
    """
    program_incremental = """
        safe(Id, t) :- safe(Id, t-1). 

        non_subset(C, Id1, t) :- conf(C), inConf(C, Id1), inConf(C, Id2), Id1 != Id2, not safe(Id2, t-1). 
        subset(C, Id1, t) :- conf(C), inConf(C, Id1), not non_subset(C, Id1, t). 

        protected(C, Id, t) :- attacks(C, Id), inConf(C, Id1), Id != Id1, attacks(C2, Id1), subset(C2, Id1, t). 
        unsafe(Id, t) :- attacks(C, Id), not protected(C, Id, t). 
        safe(Id, t) :- inConf(C, Id), not unsafe(Id, t). 

        continue(t) :- safe(Id, t), not safe(Id,t-1).

        #show continue/1.
        #show safe/2.
    """

    if not os.path.exists(ATTACKS_FILE):
        program_base += attacks
    else: ctl.load(ATTACKS_FILE)

    ctl.add("base",[],program_base)
    ctl.load(conflicts_file)
    ctl.add("step",["t"],program_incremental)
    ctl.ground([("base", [])])

    # Solve after base
    print("Step 0 ...")
    with ctl.solve(yield_=True) as handle:
        with open(TRIVIAL_EXTENSION,"w") as g:
            for model in handle:
                for atom in model.symbols(shown=True):
                    if atom.type == clingo.SymbolType.Function and atom.name == "safe" and atom.arguments[1]==clingo.Number(0):
                        assertion = atom.arguments[0]
                        print(f"grounded({assertion}).",file=g)
    # Incrementally add steps
    t = 1
    while True:
        print(f"Step {t} ...")

        # Ground the next step
        ctl.ground([("step", [clingo.Number(t)])])

        # Solve with the extended program
        with ctl.solve(yield_=True) as handle:
            for model in handle:
                atoms = set(model.symbols(shown=True))
                if clingo.Function("continue", [clingo.Number(t)]) not in atoms:
                    with open(GROUNDED_FILE,"w") as g:
                        for atom in model.symbols(shown=True):
                            if atom.type == clingo.SymbolType.Function and atom.name == "safe" and atom.arguments[1]==clingo.Number(t):
                                assertion = atom.arguments[0]
                                print(f"grounded({assertion}).",file=g)
                    return
        t+=1

def solver_grounded(conflicts_file,remaining_pans,conf_type):
    conf_name = os.path.basename(conflicts_file)
    GROUNDED_FILE=f"{SOLVER_HOME}/{conf_name}_{conf_type}_grounded_ext.lp"
    
    if not os.path.exists(GROUNDED_FILE):
        assert False
        # compute_grounded_extention(conflicts_file)
    
    ctl = clingo.Control()
    program_base = """
        appear_in_conflict(Id):-inCause(Pans,C,Id), inConf(C1,Id).
        grounded(Id) :- inCause(Pans,C,Id), not appear_in_conflict(Id).
        unsure(Pans,C) :- cause(Pans,C), inCause(Pans,C, Id), not grounded(Id). 
        grounded_ans(Pans):- cause(Pans,C), not unsure(Pans,C). 
        non_grounded_ans(Pans):- cause(Pans,C), not grounded_ans(Pans). 
    """
    program_base += remaining_pans

    ctl.add("base",[],program_base)
    ctl.load(conflicts_file)
    ctl.load(GROUNDED_FILE)
    ctl.ground([("base", [])])

    with ctl.solve(yield_=True) as handle:
        for model in handle:
            for atom in model.symbols(shown=True):
                if atom.type == clingo.SymbolType.Function and atom.name == "grounded_ans":
                    pans = atom.arguments[0]
                    print(f"SAT: {pans} is a Grounded Answer")
                elif atom.type == clingo.SymbolType.Function and atom.name == "non_grounded_ans":
                    pans = atom.arguments[0]
                    print(f"UNSAT: {pans} is not a Grounded Answer")
    return 

def trivial(conflicts_file,pans_file,conf_type):
    conf_name = os.path.basename(conflicts_file)
    ctl = clingo.Control()
    TRIVIAL_EXTENSION=f"{SOLVER_HOME}/{conf_name}_{conf_type}_trivial_ext.lp"
    program_base = """ 
    appear_in_conflict(Id):-inCause(Pans,C,Id), inConf(C1,Id).
    grounded(Id) :- inCause(Pans,C,Id), not appear_in_conflict(Id).
    unsure(Pans,C) :- cause(Pans,C), inCause(Pans,C, Id), not grounded(Id). 
    trivial_ans(Pans):- cause(Pans,C), not unsure(Pans,C).
    non_trivial_ans(Pans):- cause(Pans,C), not trivial_ans(Pans).
    """
    if not os.path.exists(TRIVIAL_EXTENSION):
        assert False
    else: ctl.load(TRIVIAL_EXTENSION)

    ctl.add("base",[],program_base)
    ctl.load(conflicts_file)
    ctl.load(pans_file)
    ctl.ground([("base", [])])

    non_trivial_ans = []
    p_ans={}
    count = 0
    with ctl.solve(yield_=True) as handle:
        for model in handle:
            
            for atom in model.symbols(shown=True):
                if atom.type == clingo.SymbolType.Function and atom.name == "trivial_ans":
                    pans = atom.arguments[0]
                    count += 1
                    print(f"SAT: {pans} is a Trivial Answer")
                elif atom.type == clingo.SymbolType.Function and atom.name == "non_trivial_ans":
                    pans = atom.arguments[0]
                    print(f"UNSAT: {pans} is not a Trivial Answer")
                    non_trivial_ans.append(pans)

                elif atom.type == clingo.SymbolType.Function and atom.name == "cause":
                    pans = atom.arguments[0]
                    if not pans in p_ans:
                        p_ans[pans] = []
                    p_ans[pans].append(f"{atom}.") 
                elif atom.type == clingo.SymbolType.Function and atom.name == "inCause":
                    pans = atom.arguments[0]
                    if not pans in p_ans:
                        p_ans[pans] = []
                    p_ans[pans].append(f"{atom}.")     
    facts = []
    for pans in non_trivial_ans:
        for fact in p_ans[pans]:
            facts.append(fact)
    return "\n".join(facts)



if __name__ == "__main__":
    SOLVER_HOME=os.path.dirname(sys.argv[0])
    if SOLVER_HOME == "":
        SOLVER_HOME="."
    args = parse_args()

    if args.conf_type == "non_binary":
        attacks = """
            non_attacking(C, Id) :- conf(C), inConf(C, Id), inConf(C, Id1), Id != Id1, pref(Id, Id1). 
            attacks(C, Id) :- conf(C), inConf(C, Id), not non_attacking(C, Id).
            """
    else: 
        attacks = """
        attacks(C, Id) :- conf(C), inConf(C, Id), inConf(C, Id1), Id != Id1, not pref(Id, Id1). 
        """
    generation_only = False

    if args.generate_attacks:
        compute_attacks(args.conflicts, args.conf_type)
        generation_only = True

    if args.generate_extension:
        compute_grounded_extention(args.conflicts, args.conf_type)
        generation_only = True
    
    if generation_only:
        exit(10)
    
    if args.repairs == TRIVIAL_GROUNDED:
        remaining_pans = trivial(args.conflicts, args.answers, args.conf_type)
        solver_grounded(args.conflicts,remaining_pans, args.conf_type)
        exit(10)
    
    ans = None
    if args.repairs == PARETO:
        ans = solver_pareto(args.conflicts,args.answers, args.semantics == BRAVE, args.reach, args.conf_type)
    elif args.repairs == COMPLETION:
        ans = solver_completion(args.conflicts,args.answers, args.semantics == BRAVE, args.reach, args.conf_type)
    else:
        proc = subprocess.Popen(["casper", "--problem", f"{SOLVER_HOME}/semantics/specific_{args.conf_type}_encodings/global/{args.semantics}_global_repair.aspq", "--files", f"{args.conflicts},{args.answers}"],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        
        stdout, stderr = proc.communicate()
        exit_code = proc.returncode
        if exit_code not in [10,20]:
            assert False
        ans = exit_code == 10
        if args.semantics == AR:
            ans = exit_code == 20

    if not ans:
        print("UNSAT:", f"Not {args.repairs} {args.semantics} Answer")
        exit(20)
    print("SAT:", f"{args.repairs} {args.semantics} Answer")
    exit(10)