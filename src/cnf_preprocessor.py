# cnf_preprocessor.py

##############################################################################################
### IMPORTS ##################################################################################

from pdb import set_trace
from .types_qbf import *

##############################################################################################
### FUNCTIONS FOR UNORDERED CNFs #############################################################

# Note: when we say orderered, we refer to the requirements of the regularize transformation
#   (from CNF to RCNF).

##############################################################################################
### TRIVIAL CNF SIMPLIFICATIONS ##############################################################

def _check_empty_clause(clauses: CNF_Formula) -> bool:
    """
    Returns True if there is an empty clause in clauses; i.e., the formula is equivalent to False.
    """
    for c in clauses:
        if not c:
            return True
    return False

def _eliminate_tautological_variables(clauses: CNF_Formula) -> int:
    """
    If v (or -v) is found several times in a clause c, only one appearence is left.
    """
    num = 0
    for i, c in enumerate(clauses):
        len_prev = len(c)
        clauses[i] = list(set(c))
        num += len_prev - len(clauses[i])
    return num

def _eliminate_tautological_clauses(clauses: CNF_Formula) -> int:
    """
    If v and -v are in the same clause c, c is removed from clauses.
    """
    num = 0
    for i, c in reversed(list(enumerate(clauses))):
        for lit in c:
            if -lit in c:
                clauses.pop(i)
                num +=1
                break
    return num

##############################################################################################
### PREPROCESSING OPERATIONS FOR QUANTIFIED CNFs #############################################

# Note: these are applicable to ordered CNFs too.

def _unit_propagation(clauses: CNF_Formula, vars2quant: Dict[PositiveInt, Quantifier]) -> Optional[bool]:
    """
    Function that performs unit propagation in case of existentially quantified formulas. I.e., if we find
    a clause with a unique literal whose variable is existentially quantified, we assign the value that makes
    that clause (or literal) true and simplify the rest of the formula accordingly (removing clauses that 
    contained the same literal and removing literals with the opposite polarity from the rest of the 
    clauses). We perform this simplification until it is not possible to be applied again. If at some point
    we obtain an empty clause, we return False directly.

    Args:
        clauses (CNF_Formula): the formula to which we will apply unit propagation.
        vars2quant (Dict[PositiveInt, Quantifier]): mapping from variables to their quantifier's type

    Returns:
        Optional[bool]: returns False if the formula is simplified to it, by means of obtaining an empty clause.
    """
    i = len(clauses) - 1
    while i >= 0:
        clause = clauses[i]
        is_unit_clause = len(clause) == 1
        #set_trace()
        v = clause[0]
        is_existential_var = vars2quant[abs(v)] == 'e'
        
        if is_unit_clause and is_existential_var:
            j = len(clauses) - 1
            while j >= 0:
                if v in clauses[j]:
                    clauses.pop(j)
                elif -v in clauses[j]:
                    clauses[j].remove(-v)
                    if not clauses[j]:
                        return False
                j -= 1

            i = len(clauses) # - 1 is done outside of the 'if' 

        i -= 1

def _any_all_universal_clause(clauses: CNF_Formula, vars2quant: Dict[int, Quantifier]) -> bool:
    """
    Function that checks if the CNF formula has some clause which only contains literals whose 
    variables are universally quantified. In that case, it returns True. The idea is that there will
    always exist an assignment that will make the clause false, making the entire formula false too, so
    it is false that the formula is satisfiable with all the possible assignments to those universally 
    quantified variables.

    Args:
        clauses (CNF_Formula): the formula to be checked.
        vars2quant (Dict[PositiveInt, Quantifier]): mapping from variables to their quantifier's type

    Returns:
        Optional[bool]: returns True if the formula has some clause that only contains variables quantified universally.
    """
    for clause in clauses:
        if all( vars2quant[abs(lit)] == 'a' for lit in clause ):
            return True
    return False

def _polarity(clauses: CNF_Formula, vars2quant: Dict[int, Quantifier]) -> Optional[bool]:
    """
    Function that for every variable checks if the variable has always the same polarity in all the literals
    where it appears in clauses. If that is the case, it can be simplified depending on its quantification:

    1. If it is existential, we can remove all the clauses that contained the variable (with the idea that
        we have assigned the appropriate value to simplify all the literals)
    2. If it is universal, we can remove all the literals that correspond to the variable (by means of
        the semantics of universally quantified formulas)

    Args:
        clauses (CNF_Formula): the formula to which we will apply simplifications with variables with singel polarities.
        vars2quant (Dict[PositiveInt, Quantifier]): mapping from variables to their quantifier's type

    Returns:
        Optional[bool]: returns False if the formula is simplified to it, by means of obtaining an empty clause.
    """
    for v in vars2quant:
        # polarities == ( [[i,j] where clauses[i,j] == v],  [[i',j'] where clauses[i',j'] == -v])
        polarities = ([], [])
        for i in range(len(clauses)):
            for j in range(len(clauses[i])):
                lit = clauses[i][j]
                assert lit != 0, "Ningún literal debería ser 0 !!!"
                # Break Precondition: tautological variables and clauses removed, so v is not several times in a clause, nor v and -v at the same time
                if lit == v:
                    polarities[0].append([i,j])
                    break
                elif lit == -v:
                    polarities[1].append([i,j])
                    break
        
        if len(polarities[0]) == 0:
            positions = polarities[1]
        elif len(polarities[1]) == 0:
            positions = polarities[0]
        else:
            # Either the case of a quantified variable that doesn't appear in the clauses
            # or the case of a variable with both polarities
            continue

        if vars2quant[v] == 'e':
            # With reversed we don't need to keep the number of removed clauses, because clause_i are ascendent (so descendent when reversed)
            for clause_i, lit_i in reversed(positions):
                clauses.pop(clause_i)
        else:
            assert vars2quant[v] == 'a', "Cuantificador desconocido !!!"
            # Since in each clause v only appears once (like v or -v), there is no index problems with pop
            for clause_i, lit_i in positions:
                clauses[clause_i].pop(lit_i)
                if not clauses[clause_i]:
                    return False

##############################################################################################
### PREPROCESSOR FOR UNORDERED CNFs ##########################################################

# Note: used in the case of the Naive solver

def preprocess(clauses: CNF_Formula, quantifiers: List[QBlock]) -> Optional[bool]:
    """
    Preprocesses the QBF formula. The clauses and quantifiers don't need to be ordered in any
    way. First, trivial simplifications of variables and clauses is performed. Then, the more
    thoughtful operations of simplifications of variables with a unique polarity, unit propagation
    and search for clauses composed uniquely by universal variables are done.

    Returns:
        Optional[bool]: returns False iff the formula has been simplified to False.
            Otherwise, it doesn't return anything.
    """
    vars2quant = {}
    for q, vars in quantifiers:
        for v in vars:
            vars2quant[v] = q

    if _check_empty_clause(clauses):
        return False
    _eliminate_tautological_variables(clauses)
    _eliminate_tautological_clauses(clauses)

    # See preprocess_ordered below for a complete explanation of the order of the simplifications.

    # In place modification to clauses
    if _polarity(clauses, vars2quant) is False:
        return False
    # In place modification to clauses
    if _unit_propagation(clauses, vars2quant) is False:
        return False
    
    if _any_all_universal_clause(clauses, vars2quant):
        return False
    

##############################################################################################
### RENAMING OF THE VARIABLES OF A CNF TO ORDER QUANTIFICATIONS ##############################

def rename_variables(quantifiers: List[QBlock], clauses: CNF_Formula) -> None:
    """
    Helper function that renames the variables so that they appear in ascending order in  
    'quantifiers'. To preserve the same quantification, we also rename the variables that 
    appear in the clauses.  

    TODO: To avoid this, it would be necessary to require .qdimacs files  
        to have the variables quantified in order. We could add this as an extra requirement  
        to our full parser, to correspondingly modify the formula files and save them.
    """
    new = 1
    old2new = {}
    varset = set()
    for (i, (_, vars)) in enumerate(quantifiers):
        for j, v in enumerate(vars):
            assert v not in varset, f"La variable {v} está cuantificada más de una vez!"
            varset.add(v)
            
            if quantifiers[i][1][j] != new:
                quantifiers[i][1][j] = new
                old2new[v] = new
            new += 1
    
    if not old2new:
        return

    for i, clause in enumerate(clauses):
        for j, lit in enumerate(clause):
            new = old2new.get(abs(lit))
            if new is not None:
                if lit > 0:
                    clauses[i][j] = new
                else:
                    clauses[i][j] = -new

##############################################################################################
### FUNCTIONS FOR THE REGULARIZE TRANSFORMATION ##############################################

def cmp_clauses(clause1: Clause, clause2: Clause) -> int:
    """
    Precondition: the literals in the clauses are ordered by their absolute values, in descending 
        order (biggest to smallest). If v is in a clause, -v is not.

    1. Variables (absolute values of literals) are ordered in descending order, since we start looking for the greatest one.
    2. If variables are equal, the negative literal preceeds the positive one.
    3. If even the literals are equal, the comparison proceeds based on the next literal of both clauses.
    4. If a clause is a prefix of the other clause, the prefix (the shortest) preceeds the longest one.

    Note:
        In the case of the prefix, it is not important that the prefix comes before or after the complete one. In the next phase,
        all complete clauses are going to be removed taking advantage of associativity and absortion, to avoid reaching a point
        in the recursion where phi_3' (the subformula that doesn't contain the variable in the next level of the tree) is false.
        It is not important but the choice has to be taken into account in the next fase. In fact, it is slightly more
        efficient to give more precedence to the prefix (as we do). That way, we will iterate reversely the list of clauses
        comparing each clause to its preceding one. If the preceding is a prefix, the current clause is deleted. As the longest clause
        is deleted and it was put closer to the end, the pop operation will have to copy leftwards one clause less.
        
        Another advantage (the real one) of giving more precedence to prefixes is that empty clauses (prefix of any other clause)
        will appear in the beginning, so it will be easy to check if we have the False literal.
    """
    len1, len2 = len(clause1), len(clause2)
    min_len = min(len1, len2)
    for i in range(min_len):
        l1, l2 = clause1[i], clause2[i]
        v1, v2 = abs(l1), abs(l2)
        if v1 < v2: return 1
        if v1 > v2: return -1
        # v1 == v2
        if l1 < l2: return -1
        if l1 > l2: return 1
        # l1 = l2 -> continue
    if len1 == len2: return 0
    if min_len == len1: return -1
    # min_len == len2
    return 1

def _is_prefix(prefix: List[int], complete: List[int]) -> bool:
    """
    Auxiliar function that checks prefix is actually a prefix of complete.

    Args:
        prefix (List[int]): the list we want to see if it is a prefix of complete.
        complete (List[int]): the reference list with which we compare prefix.

    Returns:
        bool: True iff prefix is a prefix of complete.
    """
    len_prefix = len(prefix)
    if len_prefix > len(complete):
        return False
    
    for i in range(len_prefix):
        if prefix[i] != complete[i]:
            return False
    
    return True


def absorb_with_prefixes(clauses: CNF_Formula) -> int:
    """
    Precondition: prefixes come before the complete one.

    By the property of absorbtion, we remove all other larger clauses that are preceded
    by their smallest prefix in clauses.
    
    Note: idempotence is a concrete case of absortion.
    """
    num = 0
    i = len(clauses) - 1
    while i > 0:
        complete = clauses[i]
        prefix = clauses[i-1]
        if _is_prefix(prefix, complete):
            clauses.pop(i)
            num += 1
        i -= 1
    return num

##############################################################################################
### ORDERED VERSIONS OF THE TRIVIAL CNF SIMPLIFICATIONS ######################################

def eliminate_tautological_variables_ordered(clauses: CNF_Formula) -> int:
    """
    Precondition: clauses are ordered by the variables (absolute value of literals)

    If v (or -v) is found several times in a clause c, only one appearence is left.
    """
    num = 0
    i = len(clauses) - 1
    while i >= 0:
        c = clauses[i]
        j = len(c) - 1
        while j > 0:
            if c[j-1] == c[j]:
                c.pop(j)
                num += 1
            j -= 1
        i -= 1
    return num


def eliminate_tautological_clauses_ordered(clauses: CNF_Formula) -> int:
    """
    Precondition: clauses are ordered by the variables absolute values

    If v and -v are in the same clause c, c is removed from clauses.
    """
    num = 0
    i = len(clauses) - 1
    while i >= 0:
        c = clauses[i]
        num_literals = len(c)
        j = 0
        while j < num_literals - 1:
            if c[j] == -c[j+1]:
                clauses.pop(i)
                num += 1
                break
            j += 1
        i -= 1
    return num

##############################################################################################
### PREPROCESSOR FOR ORDERED CNFs ############################################################

# Note: this version is used with the INF solvers. Although it has "ordered" in its name, it is
#   not a real precondition of the operations that are performed. The difference with the other
#   preprocessor is that we don't perform any other trivial simplification or ordering of 
#   variables, because these are already done elsewhere in the INF solvers and regularize operations.

def preprocess_ordered(clauses: CNF_Formula, quantifiers: List[QBlock]) -> Optional[bool]:
    """
    Precondition: trivial simplifications of variables and clauses have to be performed.

    Preprocesses the QBF formula. The clauses and quantifiers don't need to be ordered in any
    way. Operations of simplifications of variables with a unique polarity, unit propagation
    and search for clauses composed uniquely by universal variables are done.

    Returns:
        Optional[bool]: returns False iff the formula has been simplified to False.
            Otherwise, it doesn't return anything.
    """
    
    vars2quant = {}
    for q, vars in quantifiers:
        for v in vars:
            vars2quant[v] = q

    """
    Most appropriate order of simplifications:  
    1. Polarity: if a variable always appears with the same polarity  
        a) If existential, remove the clauses where it appears  
        b) If universal, remove the literals (checking if an empty clause remains -> False)  
    2. Unit propagation with existential variables  
        a) Remove the clauses where the literal appears with the same polarity as in the  
           unit clause (including the unit clause itself)  
        b) Remove the literals with the opposite polarity in the remaining clauses (checking  
           if any empty clause remains -> False)  
    3. Clauses with only universal variables: if there is any clause composed solely of  
       universal variables -> False  

    (3) does not modify the clauses, it only performs a check. Therefore, it does not simplify  
    the formula in a way that enables further simplification by other transformations.  

    (2) may cause more unit clauses to appear iteratively, so it must be executed multiple times.  
    It may also cause clauses with only universal variables to appear by removing existential  
    variables. Therefore, it is convenient to run it before (3). On the other hand, when detecting  
    a variable in a unit clause, all its occurrences are removed from the formula. Thus, if that  
    variable had the same polarity throughout the formula, the formula is simplified in the same  
    way as in (1). However, running (2) first does not help (1), since (2) removes all occurrences  
    of a variable and not just literals of one particular polarity, so it does not create variables  
    that previously did not have uniform polarity and now do.  

    (1) can overlap with (2) in the case mentioned above. But, regarding universal variables, it may  
    create new unit clauses of existential variables, so it is convenient to run it before (2).  
    Furthermore, if the removed existential variable was in a clause with other universal variables  
    (or alone, resulting in False due to an empty clause), the remaining clause will still consist  
    solely of universal variables, so (3) is unaffected.  

    In conclusion, the order to avoid multiple iterative calls to the same simplification without  
    losing potential simplifications is 1-2-3, where (2) is iterative only with itself.  
                                    _  
                                   \ /  
    Graph of simplifications:  1 -> 2 -> 3
    """

    # In place modification to clauses
    if _polarity(clauses, vars2quant) is False:
        return False
    # In place modification to clauses
    if _unit_propagation(clauses, vars2quant) is False:
        return False
    
    if _any_all_universal_clause(clauses, vars2quant):
        return False