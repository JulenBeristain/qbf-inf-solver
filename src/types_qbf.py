# types_qbf.py

##############################################################################################
### IMPORTS ##################################################################################

from typing import List, Tuple, TextIO, Literal, Annotated, Optional, Dict, Set, Union

##############################################################################################
### TYPE ANNOTATIONS #########################################################################

PositiveInt = Annotated[int, 'Natural1']
Variable = PositiveInt
Literal_ = Annotated[int, 'Non-zero']
Clause = List[Literal_]
CNF_Formula = List[Clause]
Tokens = List[Annotated[str, 'Non-whitespace']]
Quantifier = Literal['e', 'a']
QBlock = Tuple[Quantifier, List[Variable]]

# Note: in practice, we import every type annotation, the ones imported and defined in this file,
#   doing from types_qbf import *.