from enum import Enum
from typing import List, Union
from pddl.atomic_formula import AtomicFormula
from pddl.goal_descriptor_inequality import Inequality
from pddl.time_spec import TimeSpec


class DurationType(Enum):
    EMPTY       = "unconstrained"
    CONJUNCTION = "conjunction"
    INEQUALITY  = "inequality"
    TIMED       = "timed"


class Duration:
    """
    A class used to represent a domain duration.
    Sub-types represent one of the following types:
    - empty ()
    - conjunction (and ...)
    - inequality (> ?duration expression)
    - timed inequality (at end (> ?duration expression))
    """

    def __init__(self, duration_type : DurationType = DurationType.EMPTY) -> None:
        self.duration_type = duration_type

    def __repr__(self) -> str:
        return "()"


class DurationInequality(Duration):

    def __init__(self, inequality : Inequality) -> None:
        super().__init__(Duration.DurationType.INEQUALITY)
        self.ineq = inequality

    def __repr__(self) -> str:
        return repr(self.ineq)


class DurationTimed(Duration):

    def __init__(self, time_spec : TimeSpec, inequality : Inequality) -> None:
        super().__init__(Duration.DurationType.TIMED)
        self.time_spec = time_spec
        self.ineq = inequality

    def __repr__(self) -> str:
        return '(' + self.time_spec + ' ' + repr(self.ineq) + ')'


class DurationConjunction(Duration):

    def __init__(self, constraints : List[Union[DurationInequality,DurationTimed]] = []) -> None:
        super().__init__(Duration.DurationType.CONJUNCTION)
        self.constraints = constraints

    def __repr__(self) -> str:
        return '(and\n  ' + '\n  '.join(repr(c) for c in self.constraints) + '\n)'
