from collections import Counter
from itertools import chain, combinations
from typing import Type
from examples.create_temporal_problem import create_temporal_problem
from examples.remove_types import remove_types_from_domain, remove_types_from_problem
from pddl.atomic_formula import AtomicFormula, TypedParameter
from pddl.domain import Domain
from pddl.effect import Effect, EffectForall, EffectNegative, EffectSimple, EffectType
from pddl.goal_descriptor import GoalDescriptor, GoalDisjunction, GoalImplication, GoalNegative, GoalQuantified, GoalSimple, GoalType
from pddl.operator import Operator

def create_simple_domain():

    domain = Domain("simple_domain")

    domain.add_type("car")
    domain.add_type("city")

    domain.add_predicate_from_str("at", {"?c" : "car", "?y" : "city"})

    domain.add_operator_from_str("drive", {"?c" : "car", "?from" : "city", "?to" : "city"})
    op = domain.operators['drive']
    op.add_simple_condition_from_str("at", {"?c" : "car", "?from" : "city"})
    op.add_simple_effect_from_str("at", {"?c" : "car", "?from" : "city"}, is_delete=True)
    op.add_simple_effect_from_str("at", {"?c" : "car", "?to" : "city"})

    domain.add_operator_from_str("movetwo", {"?c" : "car", "?a1" : "city", "?a2" : "city", "?a3" : "city", "?a4" : "city"})
    op = domain.operators['movetwo']
    op.add_simple_condition_from_str("at", {"?c" : "car", "?a1" : "city"})
    op.add_simple_condition_from_str("at", {"?c" : "car", "?a2" : "city"})
    op.add_simple_effect_from_str("at", {"?c" : "car", "?a1" : "city"}, is_delete=True)
    op.add_simple_effect_from_str("at", {"?c" : "car", "?a2" : "city"}, is_delete=True)
    op.add_simple_effect_from_str("at", {"?c" : "car", "?a3" : "city"})
    op.add_simple_effect_from_str("at", {"?c" : "car", "?a4" : "city"})

    return domain


def create_nonsimple_domain():

    domain = Domain("nonsimple_domain")

    domain.add_type("block")
    domain.add_type("table")

    domain.add_predicate_from_str("on_table", {"?b" : "block", "?t" : "table"})
    domain.add_predicate_from_str("on_block", {"?b1" : "block", "?b2" : "block"})
    domain.add_predicate_from_str("clear", {"?b" : "block"})
    domain.add_predicate_from_str("destroyed", {"?b" : "block"})
    domain.add_predicate_from_str("handempty")

    domain.add_operator_from_str("destroy_all_blocks", {})
    op = domain.operators['destroy_all_blocks']
    
    op.condition = GoalImplication(
        antecedent=GoalQuantified(
            [TypedParameter("block", "?b")],
            GoalSimple(AtomicFormula.from_string("clear", {"?b" : "block"})),
            GoalType.UNIVERSAL
        ),
        consequent=GoalSimple(AtomicFormula.from_string("handempty"))
    )
    
    op.effect = EffectForall(
        [TypedParameter("block", "?b")],
        EffectSimple(AtomicFormula.from_string("destroyed", {"?b" : "block"}))
    )
    
    return domain

def simplify_implication_conditions(condition : GoalImplication, operator : Operator) -> None:
    """
    Simplifies implied conditions.
    """
    new_condition = GoalDisjunction([GoalNegative(condition.antecedent), condition.consequent])
    operator.condition = new_condition

# =================== #
# invariant synthesis #
# =================== #

class CandidateInvariant():
    def __init__(self, pred_name : str, params: list[TypedParameter], counted_labels : list[str]):
        self.invariant = {pred_name: counted_labels}
        self.counted_labels = {}
        for i, l in zip(counted_labels, [params[p].label for p in counted_labels]):
            self.counted_labels[l] = {pred_name: i}
        self.params = {pred_name: params}
        #self.counted_labels = counted_labels
    
    def add_atom(self, pred_name, params: list[TypedParameter], counted_labels : list[str]):
        self.invariant[pred_name] = counted_labels
        for i, l in zip(counted_labels, [params[p].label for p in counted_labels]):
            self.counted_labels[l] = {pred_name: i}

    def __repr__(self) -> str:
        return "∀" + ", ".join([str(i) for i in self.counted_labels.keys()]) + " : " + str(self.invariant)


def get_modifiable_predicates(effect : EffectSimple, modifiable_predicates : list):
    """
    Returns the list of modifiable predicates in the effect.
    """
    modifiable_predicates.add(effect.formula.name)
    
def collect_candidate_effects(effect : Effect, candidate : CandidateInvariant, add_list : list[Effect], delete_list : list[Effect]):
    """
    Collects candidate effects.
    """
    if isinstance(effect, EffectNegative):
        # check if formula matches a candidate
        if effect.formula.name in candidate.invariant.keys():
            delete_list.append(effect.formula)
    elif isinstance(effect, EffectSimple):
        # check if formula matches a candidate
        if effect.formula.name in candidate.invariant.keys():
            add_list.append(effect.formula)

def is_operator_too_heavy(operator : Operator, candidate : CandidateInvariant) -> bool:
    """
    Returns True if the invariant is heavy.
    """
    adds : list[AtomicFormula] = []
    operator.visit(collect_candidate_effects, valid_types=(EffectSimple), kwargs={'add_list': adds, 'delete_list': []}) 
    for prop1 in adds:
        for prop2 in adds:
            # different predicates are added
            if prop1.name != prop2.name:
                return True
            # predicates possibly have different parameters
            for i, (param1, param2) in enumerate(zip(prop1.typed_parameters, prop2.typed_parameters)):
                if i in candidate.invariant[prop1.name]:
                    continue
                if param1.label != param2.label:
                    return True
    return False
            
def is_add_effect_unbalanced(o : Operator, effect : Effect, candidate : CandidateInvariant) -> bool:
    adds : list[AtomicFormula] = []
    dels : list[AtomicFormula] = []
    operator.visit(collect_candidate_effects, valid_types=(EffectSimple), kwargs={'add_list': adds, 'delete_list': dels})
    



    for c_name, cl in candidate.invariant.items():
        
        other = None
        for prop in adds:
            if prop.name != c_name:
                continue
            if not other: other = prop
            # Check if parameters match
            match = True
            for index in cl:
                if prop.typed_parameters[index].label != other.typed_parameters[index].label:
                    match = False
                    break
            if not match: continue
            weight += 1
            if weight >= 2: 
                break
    

if __name__ == "__main__":

    domain = create_simple_domain()

    # Normalise the problem, removing types and simplifying conditions
    remove_types_from_domain(domain)
    for _, op in domain.operators.items():
        op.visit(simplify_implication_conditions, valid_types=(GoalImplication), args=(op,))

    print("Modifiable Predicates")
    modifiable_predicates = set()
    domain.visit(get_modifiable_predicates, valid_types=(EffectSimple), args=(modifiable_predicates,))
    print(modifiable_predicates)

    print("Initial Candidates")
    candidates = []
    for pred in modifiable_predicates:
        predicate = domain.predicates[pred]
        powerset = list(chain.from_iterable(combinations(range(len(predicate.typed_parameters)), r) for r in range(1,len(predicate.typed_parameters)+1)))
        for combination in powerset:
            candidates.append(CandidateInvariant(pred, predicate.typed_parameters, [p for p in combination]))
    print(candidates)

    print("Proving Invariants")
    proved_candidates = []
    for candidate in candidates:
        balanced = True
        for operator in domain.operators.values():
            adds, dels = [], []
            operator.visit(collect_candidate_effects, valid_types=(EffectSimple), kwargs={'add_list': adds, 'delete_list': dels})
            
            # for c_name, cl in candidate.invariant.items():
            #     operator.visit(get_modified_predicates, valid_types=(EffectSimple), args=(c_name, adds, dels))
            #     [for prop in adds]
                # for prop in dels:
                #     for other in adds:
                #         if prop.name != other.name and prop.name != c_name:
                #             continue
                #         match = True
                #         for index in cl:
                #             if prop.typed_parameters[index].label != other.typed_parameters[index].label:
                #                 match = False
                #                 break
                #         if not match: continue
                #         adds.remove(other)
                #         break
            if len(adds) > 0:
                balanced = False
                break
        if not balanced:  # Not balanced, so we try to refine it
            
            candidates.append(refinement)
            continue
        
        for operator in domain.operators.values():

        if weight < 2: proved_candidates.append(candidate)


    print(proved_candidates)