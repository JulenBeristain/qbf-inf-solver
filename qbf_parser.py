# qbf_parser.py

##############################################################################################
### PUBLIC FUNCTIONS (when import *) #########################################################
__all__ = ['read_qdimacs_from_file', 'read_qdimacs_from_str', 'read_qdimacs',
           'read_qdimacs_from_file_unchecked', 'read_qdimacs_from_str_unchecked',
           'read_qcir_from_file', 'read_qcir_from_str', 'read_qcir',
           'read_qcir_from_file_unchecked', 'read_qcir_from_str_unchecked',
           'read_qaiger_from_file', 'read_qaiger_from_str', 'read_qaiger',
           'read_qaiger_from_file_unchecked', 'read_qaiger_from_str_unchecked']

##############################################################################################
### IMPORTS ##################################################################################
import os
from enum import Enum
import subprocess
from types_qbf import *

##############################################################################################
### AUXILIAR CLASSES #########################################################################

# Enumeration that represents the state of the processing in _read_qdimacs_from_str
class Processing(Enum):
    HEADER = 1
    QBLOCKS = 2
    CLAUSES = 3

### EXCEPTIONS ###############################################################################
class IncorrectFileFormatError(Exception):
    """Exception when the input file is not in QDIMACS format."""
    pass

##############################################################################################
### GLOBAL AUXILIARY VARIABLES ###############################################################
_current_line: int = -1

##############################################################################################
### AUXILIARY PRIVATE FUNCTIONS (leading _) ##################################################

### SKIP EMPTY LINES AND COMMENTS ############################################################

def _is_comment(line: str) -> Tuple[bool, Tokens]:
    """
    Auxiliar function that checks if the line is an empty line or a comment line, or, on the 
    other hand, it is the end of file or a line with contents.

    Args:
        line (str): a line of the QDIMACS file's content.

    Returns:
        bool: True if line is a comment. False if it is the end of file (empty string) 
            or a line with contents.
        Tokens: not an empty list iff the line has contents. In that case, the tokens of the line
            splitted by whitespaces.

    Raises:
        IncorrectFileFormatError: if an empty line is found.
    """
    # End of file
    if line == "": return False, []

    line = line.strip()
    # Empty line
    if line == "": raise IncorrectFileFormatError(f'[Line {_current_line}]: Empty lines are not allowed!')
    
    tokens = line.split()
    # Comment line
    if tokens[0] == 'c': return True, []

    # Line with contents
    return False, tokens

def _skip_comments(f: TextIO) -> Tokens:
    """
    Auxiliary function checks if there is no empty line, lines with only whitespaces,
    and skips comments (lines that start with 'c').

    Args:
        f (TextIO): the file handler.

    Returns:
        Tokens: The tokens (whitespaces as separator) of the first line with contents that is found.
            If it arrives to the end of the file, an empty list is returned.
    """
    while True:
        line = f.readline()
        _current_line += 1

        is_comment, tokens = _is_comment(line)
        if not is_comment:
            return tokens
        
def _check_not_comments(f: TextIO) -> Tokens:
    """
    Auxiliary function checks if there is no empty line, lines with only whitespaces,
    nor comments (lines that start with 'c').

    Args:
        f (TextIO): the file handler.

    Returns:
        Tokens: The tokens (whitespaces as separator) of the next correct line (line with contents or EOF).
            If it arrives to the end of the file, an empty list is returned.

    Raises:
        IncorrectFileFormatError: if a comment or an empty line is found.
    """
    line = f.readline()
    _current_line += 1

    is_comment, tokens = _is_comment(line)
    if is_comment:
        raise IncorrectFileFormatError(f'[Line {_current_line}]: comments can not appear below the header line!')

    return tokens

##############################################################################################
### HEADER LINE ##############################################################################

def _process_header_line_tokens(tokens: Tokens) -> Tuple[PositiveInt, PositiveInt]:
    """
    Auxiliar function that checks if tokens is a valid header line.

    Args:
        tokens (Tokens): the tokens of the first line with contents of the QDIMACS file.

    Returns:
        PositiveInt: number of variables indicated in the header line.
        PositiveInt: number of clauses indicated in the header line.

    Raises:
        IncorrectFileFormatServer: when the file is empty or the file does not have the header line
        ValueError: 
            When the numbers of variables and clauses is not specified correctly.
            
            When the numbers of variables and clauses are incorrect: they are not both positive; or 
            if num_clauses is zero then num_vars is not zero.
    """
    # End of file
    if not tokens: raise IncorrectFileFormatError('Empty file!')

    # Incorrect line
    if len(tokens) != 4 or tokens[0] != 'p' or tokens[1] != 'cnf':
        raise IncorrectFileFormatError('The file does not have the header file!')
    
    num_vars = int(tokens[2])
    num_clauses = int(tokens[3])

    if num_vars < 0 or num_clauses < 0 or (num_vars > 0 and num_clauses == 0):
        raise ValueError(f'Header line - incorrect (num_vars, num_clauses) = {(num_vars, num_clauses)}. '
                          'Three options:\n'
                          '\t1. num_vars > 0, num_clauses > 0 (non trivial)\n'
                          '\t2. num_clauses = 0, num_vars = 0\n (true literal)'
                          '\t3. num_vars = 0, num_clauses > 0 (empty clauses -> false literal)\n')
    
    return num_vars, num_clauses

def _process_header_line(f: TextIO) -> Tuple[PositiveInt, PositiveInt]:
    """
    Auxiliar function that processes the file until the header line is found.

    Args:
        f (TextIO): the file handler.

    Returns:
        PositiveInt: number of variables indicated in the header line.
        PositiveInt: number of clauses indicated in the header line.

    Raises:
        IncorrectFileFormatServer: when the file is empty or the file does not have the header line
        ValueError: 
            When the numbers of variables and clauses is not specified correctly
            
            When the numbers of variables and clauses are incorrect. Both must be positive or zero
            at the same time.
    """
    while True:
        tokens = _skip_comments(f)
        return _process_header_line_tokens(tokens)

##############################################################################################
### BLOCKS OF QUANTIFIERS ####################################################################

def _process_quantifying_block_tokens(
        tokens: Tokens, quantifiers: List[QBlock], num_vars:int,
        pre_q: Quantifier) -> Tuple[Optional[Quantifier], Tokens]:
    """
    Auxiliary function that processes the block of quantifiers in a single line stored in tokens.
    Quantifier blocks are added to their list.

    Args:
        tokens (Tokens): the tokens that contain the quantifying block.
        quantifiers (List[QBlock]): the list of the quantifier blocks.
        num_vars: number of variables specified in the header line.
        pre_q (Quantifier): the quantifier of the previous quantifying line.

    Returns:
        Optional[Quantifier]: the quantifier of the line tokens represents. None if it is not a quantifying line. 
        
        Tokens: If the tokens correspond to a quantifying line an empty list is returned because the input tokens
            have already been used to complete quantifiers. Otherwise, the list of tokens of the first line after 
            the quantifying lines. Empty list if end of file.
            
    Raises:
        IncorrectFileFormatError: 
            If the quantifying line does not end with '0'.
            If a quantifying block is empty (only q 0).
            If any quantified variable is out of the [1,num_vars] interval
        ValuerError: if some variable is not represented with a number.
    """
    # End of file
    if not tokens: return None, tokens
    
    # End of quantifying blocks
    q = tokens[0]
    if q != 'e' and q != 'a': return None, tokens

    # Does not end with zero
    if tokens[-1] != 0: 
        raise IncorrectFileFormatError(f'[Line {_current_line}]: Quantifying lines must end with 0!')

    # Empty quantifying block
    if len(tokens) == 2:
        raise IncorrectFileFormatError(f'[Line {_current_line}]: empty quantifying block is invalid!')
    
    quantified_vars =  [int(t) for t in tokens[1:-1]]
    # Check if all of them are between 1 and num_vars
    for v in quantified_vars:
        if v < 1 or num_vars < v:
            raise IncorrectFileFormatError(
                f'[Line {_current_line}]: only variables from 1 to num_vars={num_vars} can be quantified!')

    # Otherwise, it is a quantifying line
    try:
        if pre_q != q:
            quantifiers.append((q, quantified_vars))
        # Consecutive blocks of the same type are unified
        else:
            quantifiers[-1][1].extend(quantified_vars)
    
    except ValueError as e:
        raise ValueError(f'[Line {_current_line}]: all variables that are quantified have to be positive integers!')

    return q, []

def _process_quantifying_blocks(f: TextIO, quantifiers: List[QBlock], num_vars: int) -> Tokens:
    """
    Auxiliary function that processes the block of quantifiers in the file. Quantifier blocks are added to
    their list.

    Args:
        f (TextIO): the file handler.
        quantifiers (List[QBlock]): the list of the quantifier blocks.
        num_vars: number of variables specified in the header line.

    Returns:
        Tokens: the list of tokens of the first line after the quantifying lines. Empty list if end of file.

    Raises:
        IncorrectFileFormatError: if a quantifying line does not end with '0'.
        ValuerError: if some variable is not represented with a number.
    """
    pre_q = ''
    while True:
        tokens = _check_not_comments(f)
        q, tokens = _process_quantifying_block_tokens(tokens, quantifiers, num_vars, pre_q)
        # The line was not a quantifying block (end of file or beginning of clauses) = End of block of quantifiers
        if q is None:
            return tokens
        pre_q = q

def _validate_quantifiers(quantifiers: List[QBlock], num_vars: PositiveInt) -> None:
    """
    Auxiliary function that validates if the quantifiers is correct and consistent with the number of variables.

    Assumptions:
    - All variables are quantified, from 1 to num_vars.
    - Each variable is quantified once only.

    Args:
        quantifiers (List[QBlock]): Blocks of quantifiers, 'e' for existential and 'a' for universal.
        num_vars (PositiveInt): number of variables that the function ought to have according to the header file.
    
    Raises:
        IncorrectFileFormatError: 
            If some variable is quantified more than once.

            If some variable is not quantified, it is free. Exception: if no variable is quantified,
            i.e., we had a DIMACS file, we accept it and add a single existential block with all variables.
    """
    # Validate: all variables are quantified, from 1 to num_vars; each variable is quantified once
    vars = set()
    for qs, qvars in quantifiers:
        for v in qvars:
            if v in vars:
                raise IncorrectFileFormatError(f'[Line < {_current_line}]: Each variable has to be quantified only once!')
            vars.add(v)
    if len(vars) != num_vars and quantifiers:
        free_vars = set(range(1, num_vars + 1)) - vars
        raise IncorrectFileFormatError(
            f'[Line < {_current_line}]: All variables have to be quantified! Free variables are not allowed!\n'
            f'Free variables: {free_vars}')

    # If there was no block of quantifiers (but at least one variable) we add an existential with all the variables
    if (not quantifiers) and (num_vars > 0):
        quantifiers.append(('e', [i for i in range(1, num_vars + 1)]))

##############################################################################################
### CLAUSES ##################################################################################

def _process_clause_tokens(tokens: Tokens, clauses: CNF_Formula, num_vars: PositiveInt) -> None:
    """
    Auxiliary function that processes the a line containing a clause in the QDIMACS file. The list
    of clauses is completed with the clause contained in tokens.

    Args:
        tokens (Tokens): the tokens of the line that contains the clause. It is not the empty list;
            i.e., we know that we are not processing the end of file, but a line with contents.
        clauses (CNF_Formula): the list of clauses.
        num_vars (PositiveInt): the number of variables in the formula specified in the header.

    Raises:
        IncorrectFileFormatError: 
            If a clause line does not end with '0'.

            If another quantifying block comes after the description of clauses has started;
            i.e., the formula is not in PRENEX Normal Form.
            
            If there is some variable outside of the interval [1, num_vars]
        ValueError: If some variable in a clause is not expressed with an integer.
    """
    # Does not end with zero
    if tokens[-1] != 0: raise IncorrectFileFormatError(f'[Line {_current_line}]: Clause lines must end with 0!')

    # It is not in PRENEX
    if tokens[0] == 'e' or tokens[0] == 'a':
        raise IncorrectFileFormatError(f'[Line {_current_line}]: The formula has to be in PRENEX Normal Form. '
        'Quantifiers are only allowed before any clause is described.')
    
    clause = [None] * (len(tokens) - 1)
    for i in range(len(tokens) - 1):
        try:
            v = int(tokens[i])
        except ValueError as e:
            raise ValueError(f'[Line {_current_line}]: all variables have to be expressed as ints between 1 and num_vars!')
        abs_v = abs(v)
        if abs_v < 1 or abs_v > num_vars:
            raise IncorrectFileFormatError(f'[Line {_current_line}]: all variables have to be between 1 and num_vars!')
        clause[i] = v

    clauses.append(clause)

def _process_clauses(f: TextIO, clauses: CNF_Formula, tokens: Tokens, num_vars: PositiveInt) -> None:
    """
    Auxiliary function that processes the block of clauses in the QDIMACS file, until the end of the file.
    The list of clauses is completed with the cnf formula expressed in the file.

    Args:
        f (TextIO): the file handler.
        clauses (CNF_Formula): the list of clauses.
        tokens (Tokens): the tokens of the first line after the block of quantifiers.
        num_vars (PositiveInt): the number of variables in the formula specified in the header.

    Raises:
        IncorrectFileFormatError: 
            If a clause line does not end with '0'
            
            If another quantifying block comes after the description of clauses has started;
            i.e., the formula is not in PRENEX Normal Form.
            
            If there is some variable outside of the interval [1, num_vars]
        ValueError: if some variable in a clause is not expressed with an integer.
    """
    while True:
        # Do not forget the tokens of the no quantifying line (*2)
        # End of file
        if not tokens: return

        _process_clause_tokens(tokens, clauses, num_vars)
        
        # We do not skip the first line after the block of quantifiers (*2)
        tokens = _check_not_comments(f)

def _validate_clauses(clauses: CNF_Formula, num_vars: PositiveInt, num_clauses: PositiveInt) -> List[List[Clause]]:
    """
    Auxiliary function that validates the list of clauses obtained. It has to have num_clauses clauses and
    num_vars variables.

    Args:
        clauses (CNF_Formula): the list of clauses to be validated.
        num_vars (PositiveInt): number of variables specified in the header line (that clauses ought to have).
        num_clauses (PositiveInt): number of clauses sepcified in the header line (that clauses ought to have).
    
    Returns:
        List[List[Clause]]: a list (working as a dictionary) that maps each variable to the references of the clauses that
            contain that variable (useful if the formula is going to be simplified in the next step). We use a list instead
            of a dictionary because it is more efficient as in this case we know that the keys range from 1 to num_vars (we
            will have a hole in the first index 0).

            Another possibility would have been to return a List[Index]. Instead of  references to the clauses we could
            have stored the indexes of the clauses. In this case, when simplifying the formula, if some repeated clauses
            were removed, the indexes greater than the minimum clause removed would have to be reduced by the amount of 
            removed clauses.
            
    Raises:
        IncorrectFileFormatError: 
            When the number of clauses does not mathc num_clauses
            
            When there is some variable ouf of the [1, num_vars] interval
            
            When there is some variable in the [1, num_vars] interval that is not used
    """
    if len(clauses) != num_clauses:
        raise IncorrectFileFormatError('The number of clauses found does not match with the '
        'indicated in the header line!')
    
    # Dictionary: var -> [clauses] (useful in the simplifying step instead of a simple set)
    v2c = [None] + [[] for _ in range(num_vars)]
    varset = set()
    for i, c in enumerate(clauses):
        for v in c:
            abs_v = abs(v)
            varset.add(abs_v)
            v2c[abs_v].append(c)
    if len(varset) != num_vars:
        unused_variables = set(range(1, num_vars + 1)) - varset
        raise IncorrectFileFormatError('Clauses: There can not be any unused variable!\n\n'
                                       f'Unused variables: {unused_variables}')
    return v2c

##############################################################################################
### FORMULA SIMPLICATION (without any value assignment) ######################################

def _check_empty_clause(clauses: CNF_Formula) -> bool:
    """
    Auxiliar function that checks if there is some empty clause in the formula. If thats the case, the entire
    formula is simply equivalent to the False literal, because the neutral element of disyunction (the only
    operation in clauses) is False and because the dominant element of conjunction (the only operation between
    clauses in a formula in CNF) is precisely False.

    Args:
        clauses (CNF_Formula): clauses of the formula in cnf
    
    Returns:
        bool: True iff there is some empty clause.
    """
    return any(len(c) == 0 for c in clauses)

def _remove_repeated_variables(clauses: CNF_Formula) -> bool:
    """
    Auxiliar function that removes repeated variables from the clauses. The number of variables and clauses of the
    formula are not affected.

    Args:
        clauses (CNF_Formula): clauses of the formula in cnf
    
    Returns:
        bool: True iff the formula was simplified
    """
    simplified = False
    for i, c in enumerate(clauses):
        clauses[i] = list(set(c))
        simplified |= len(c) != len(clauses[i])
    return simplified

##############################################################################################

def _remove_repeated_clauses(clauses: CNF_Formula, num_clauses: PositiveInt) -> Tuple[PositiveInt, bool]:
    """
    Auxiliar function that removes repeated clauses. The number of variables remains the same, but the number of 
    clauses might be reduced.
    
    Precondition:
        To ease the comparison between clauses and avoid repeated sorting with the same formulas, all the clauses
        have been sorted.

    Detail:
        Clauses are removed from the end of the list to reduce the cost of pop. This is important too for the dictionary
        from variables to references of clauses created in _validate_clauses, because clauses were inserted in order. That
        way, the dictionary will not keep references to equivalent clauses that are removed.

        Extra: if for v2c the other option of indexes was selected, before returning the indexes of the clauses that come
        after the removed duplicated clauses would have to be decremented by the number of removed clauses.

    Args:
        clauses (CNF_Formula): clauses of the formula in cnf
        num_clauses (PositiveInt): number of clauses in clauses

    Returns:
        PositiveInt: the number of clauses of the simplified formula
        bool: True iff the formula was simplified
    """
    num_removed = 0
    i = 0
    while i < len(clauses):
        for j in range(len(clauses)-1, i, -1):
            if clauses[j] == clauses[i]:
                clauses.pop(j)
                num_removed += 1
        i += 1
    return num_clauses - num_removed, num_removed > 0

##############################################################################################

def _remove_tautological_clauses(
        clauses: CNF_Formula, quantifiers: List[QBlock], num_vars: PositiveInt, num_clauses: PositiveInt, 
        v2c: List[List[Clause]]) -> Tuple[PositiveInt, PositiveInt, bool]:
    """
    Auxiliar function that removes tautological clauses; i.e., clauses that contain a variable and its negated literal,
    v and -v. Both the number of variables and the number of clauses might be affected. The second one is self-explanatory.
    The first one is reduced if the variable is contained only in tautological clauses. If some variable v < num_vars is removed, 
    the variables greater than v are decremented to keep the property that all variables range from 1 to num_vars'.

    Detail:
        Clauses are checked in reverse order to reduce the cost of pop and do not need to adjust the index in the loop.

        Extra detail:
            If we had implemented the other possibility of v2c as List[Index] (with the corrected indexes in _remove_repeated_clauses),
            the search for c by identity in the list of clauses in the removed variables would not be needed.

    Precondition:
        The clauses are sorted based on the absolute value of the literals, (additionally, there is no repeated variables).
        That way, tautological clauses can be found looking all consecutive pairs of numbers.
        Another precondition is that the clauses in v2c the clauses are ordered (see _validate_clauses), so removing tautological clauses
        in reverse order may be more efficient if 

    Args:
        clauses (CNF_Formula): clauses of the formula in cnf
        quantifiers (List[QBlock]): block of quantifiers of the formula
        num_vars (PositiveInt): number of variables in the formula
        num_clauses (PositiveInt): number of clauses in clauses
        v2c (List[List[Clauses]]): mapping from variables that appear in the formula (from 1 to num_vars) to the list of references 
        to the clauses that contain the key variables.

    Returns:
        PositiveInt: the number of variables in the simplified formula
        PositiveInt: the number of clauses of the simplified formula
        bool: True iff the formula was simplified
    """
    removed_clauses = removed_vars = 0
    min_removed = float('inf')
    for i in range(num_clauses-1, -1, -1):
        c = clauses[i]
        for j in range(len(c)-1):
            if c[j] == -c[j+1]:
                # Remove tautological clause
                clauses.pop(i)
                removed_clauses += 1

                # Check if some variable in the clause is not present in any other clause
                # Important detail: repeated variables are removed, so we do not try to remove the same clause more than once
                for v in c:
                    abs_v = abs(v)
                    # To avoid comparing lists by value with remove, we compare them by identity to find the index and use pop
                    # We can do this because the duplicated clauses were removed leaving the first occurrence, which is exactly
                    # the occurrence whose reference was stored in v2c.
                    index_c = next(i for i, clause in enumerate(v2c[abs_v]) if clause is c)
                    v2c[abs_v].pop(index_c)
                    if not v2c[abs_v]:
                        removed_vars += 1
                        if abs_v < min_removed:
                            min_removed = abs_v
                break
    num_clauses -= removed_clauses
    num_vars -= removed_vars

    # Decrement variables greater than min_removed by removed_vars to keep variables from 1 to num_vars' both
    # in the simplified clauses and in the quantifier blocks
    if removed_vars > 0:
        for c in clauses:
            for i, l in enumerate(c):
                if l > min_removed:
                    c[i] -= removed_vars
                elif l < -min_removed:
                    c[i] += removed_vars
        
        for qs, qvars in quantifiers:
            for i, v in enumerate(qvars):
                if v > min_removed:
                    qvars[i] -= removed_vars

    return num_vars, num_clauses, removed_clauses > 0

##############################################################################################
##############################################################################################

def _simplify_formula(
        clauses: CNF_Formula, quantifiers: List[QBlock], num_vars: PositiveInt, num_clauses: PositiveInt, 
        v2c: List[List[Clause]]) -> Tuple[PositiveInt, PositiveInt, bool]:
    """
    Auxiliar function that applies simplifications to a valid cnf formula that do not need any assignment for any
    variable; i.e., remove repeated variable; remove repeated clauses; and simplify tautological clauses, clauses 
    that contain v and -v. The number of variables and number of clauses are adjusted accordingly.

    Args:
        clauses (CNF_Formula): the list of clauses of the formula.
        quantifiers (List[QBlock]): the quantifier blocks of the formula.
        num_vars (PositiveInt): number of variables in clauses (variables go from 1 to num_vars).
        num_clauses (PositiveInt): number of clauses in clauses.
        v2c (List[List[Clause]]): mapping from variables that appear in the formula (from 1 to num_vars) to the list of references 
        to the clauses that contain the key variables.

    Detail:
        If some 

    Returns:
        PositiveInt: num_vars adjusted if all appearences of some variable are completely removed. See that if a variable v
            where v < num_vars is removed, the variables in the final state of clauses that are greater than v are
            adjusted (-1) to keep the property that no variable from 1 to num_vars' is unused.
        PositiveInt: num_clauses adjusted taking into account the number of repeated and tautological clauses that have 
            been removed.
        bool: True iff the formula was simplified
    """
    if _check_empty_clause(clauses):
        clauses.clear()
        clauses.append([])
        quantifiers.clear()
        return 0, 1, True

    simplified1 = _remove_repeated_variables(clauses)
    
    # To ease comparison of clauses to remove duplicates and identification of tautological clauses
    for c in clauses:
        c.sort(key=lambda n: abs(n))
    
    num_clauses, simplified2 = _remove_repeated_clauses(clauses, num_clauses)
    num_vars, num_clauses, simplified3 = _remove_tautological_clauses(clauses, quantifiers, num_vars, num_clauses, v2c)
    return num_vars, num_clauses, simplified1 or simplified2 or simplified3

##############################################################################################
### STORE THE SIMPLIFIED FORMULA IN A NEW FILE ###############################################

def _get_unique_filename(file_path: str, suffix: str = "_s") -> str:
    """
    Auxiliar function that returns a unique file name that starts with file_path with an extra identifying suffix.
    
    Args:
        file_path (str): the file path of the original file
        suffix (str): by default _s

    Returns:
        str: the unique name for the simplified formula, f'{file_path_without_extension}_s{N}.{extension}'.
    """
    directory, filename = os.path.split(file_path)
    name, ext = os.path.splitext(filename)

    # Iterate over numbers until finding a unique filename
    n = 1
    while True:
        new_filename = f"{name}{suffix}{n}{ext}"
        new_filepath = os.path.join(directory, new_filename)

        if not os.path.exists(new_filepath):
            return new_filepath

        n += 1

def _write_simplified_formula(
        file_path: str, num_vars: PositiveInt, num_clauses: PositiveInt, 
        quantifiers: List[QBlock], clauses: CNF_Formula) -> str:
    """
    Auxiliar function that writes the given CNF formula to a file in QDIMACS format. We ensure that the file
    is a unique one, so no content of an already existing file is lost. Specifically, the new file is named
    f'{file_path_without_extension}_s{N}.{extension}'. We ensure that N is greater than any other copy of the
    secure version of the file.

    Args:
        file_path (str): the path of the original file
    	num_vars: number of vars in the given formula
        num_clauses: number of clauses in the given formula
        quantifiers: the quantifying blocks that are applied to the formula (PRENEX Normal Form)
        clauses: the clauses of the formula in CNF

    Returns:
        str: the name of the new file that contains the simplifying formula
    """
    name = _get_unique_filename(file_path)
    with open(name, 'w') as f:
        # Header line
        f.write(f'p cnf {num_vars} {num_clauses}\n')
        # Quantifying blocks
        for q, vars in quantifiers:
            f.write(f'{q} {" ".join(map(str, vars))} 0\n')
        # Clauses
        for c in clauses:
            f.write(f'{" ".join(map(str, c))} 0\n')
    return name

##############################################################################################
### PUBLIC FUNCTIONS #########################################################################

### QDIMACS ##################################################################################

def read_qdimacs_from_file(file_path: str, simplify: bool = True) -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Function that reads the QBF instance stored in 'file_path'.

    Assumptions:
        - The file starts with the header line: p cnf num_vars num_clauses
        - The number of variables and clauses indicated in the header correspond to the real numbers.
        - Variables range from 1 to num_vars, all of those integers are used.
            - True literal is expressed as: p cnf 0 0
            - False literal can be expressed with a contradiction: p cnf 1 2; 1 -1
        - The formula is in Prenex CNF; i.e., all the quantifiers appear before the clauses.
        - Each variable is quantified only once.
        - All variables are quantified, there is not any free variable.
        - The quantifier blocks and clauses end with 0, and they are in separated lines.
        - Comments can only appear before the header line.
        - Empty lines are not accepted.

    Details:
        - All white spaces and empty lines are ignored. Comments, lines that start with 'c', are ignored too.
        - Assumptions are validated.
        - If consecutive blocks of quantifiers have the same quantifier they are unified.
        - If there is no block of quantifiers (the file is in DIMACS instead of QDIMACS) an existencial
        block containing all the variables is returned.
        - When simplify is activated:
            - If a clause contains a variable and its negation it is a tautology and therefore it is not included
            in the final list of clauses.
                - If that was the only appearence of the variable, the greatest variable has to be adjusted to be
                represented with this eliminated variable, and the number of variables and clauses have to be 
                decremented accordingly. This is done once per each variable and clause that is eliminated. (*1)
            - If a clause contains the same variable several times, only one appearence is kept.
            - If the same clause is repeated several times, only one is kept.
            - Variables are sorted within each clause according to the absolute values (variables themselves, not literals).

    Extra detail:
        If the formula is simplified, it may be the case that some variable was removed and that the variables that
        were greater than it have been decremented, so now they are identified with different integers. That is why in that
        case the simplified formula is stored in a different file.

        The quantifying blocks might be simplified too, but as compacted and not compacted versions are completely equivalent,
        we do not store the new file unless the formula is further simplified.
            
    Args:
        file_path (str): The name of the file in QDIMACS format.
        simplify (bool): True by default. In case the formula is not simplified, simple simplifications that do not
            requiere any value assignment is performed: remove repeated variables in clauses; remove repeated 
            clauses; and remove tautological clauses, which contain v and -v.

    Returns:
        PositiveInt: the number of (not tautological (*1)) variables in the formula.
        PositiveInt: the number of (not tautological (*1)) clauses in the formula.
        CNF_Formula: the list of clauses, where literals are represented with integers. Positive integers for
            variables and negavite integers for negated variables.
        List[QBlock]: the list of quantifier-blocks. Each block is a duple. The first element is
            'e' for exisTODOtential blocks and 'a' for universal blocks. The second element is the list of variables
            quantified in that block.
    
    Raises:
        FileNotFoundError: no file is found in file_path. 
        ValueError: 
            When a literal was expected a non-integer string is found.
            
            When the number of variables or clauses is negative, or when num_clauses is zero and the other is positive.
        IncorrectFileFormatError: the input file does not follow the QDIMACS format and the aforementioned assumptions.
    """
    clauses = []
    quantifiers = []

    # To improve errors and to ease detection of QDIMACS incompatibilities to the user.
    # Made global to avoid passing as a parameter and having an extra returning value in all the auxiliary functions.
    _current_line = 0

    with open(file_path, "r") as f:
        # First, the header line
        num_vars, num_clauses = _process_header_line(f)

        # Second, the quantifying blocks
        tokens = _process_quantifying_blocks(f, quantifiers, num_vars)

        _validate_quantifiers(quantifiers, num_vars)

        # Finally, clauses
        _process_clauses(f, clauses, tokens, num_vars)
       
        # Validate: all variables appear, from 1 to num_vars. The number of clauses is correct too
        vars2clauses = _validate_clauses(clauses, num_vars, num_clauses)

        # Simplify formula
        if simplify:
            num_vars, num_clauses, simplified = _simplify_formula(clauses, quantifiers, num_vars, num_clauses, vars2clauses)
            if simplified:
                name = _write_simplified_formula(file_path, num_vars, num_clauses, quantifiers, clauses)
                print("WARNING: The file contains a formula that has been simplified, without any need to "
                      "assign a value for any variable; i.e., repeated vars and clauses have been removed, "
                      "as well as tautological clauses (those that contain v and -v).\n\n"
                      f"Name of the new file: {name}")

    return num_vars, num_clauses, clauses, quantifiers

##############################################################################################

def read_qdimacs_from_str(contents: str, simplify: bool = True) -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    The version of read_qdimacs_from_file that takes all the content of the file directly. Useful to work with format conversors
    (from QCIR and QAIGER to QDIMACS) that print all the content in standard output.

    The from_file version could be implemented using this one, after storing all the contents returned by f.write in a string 
    variable. But using f.readline and going line by line has the advantage of not using all the memory needed to store
    all the contents of the file. 
    """
    clauses = []
    quantifiers = []

    # To improve errors and to ease detection of QDIMACS incompatibilities to the user.
    # Made global to avoid passing as a parameter and having an extra returning value in all the auxiliary functions.
    _current_line = 0

    # This version of the parser will work as a simple linear state machine with three states, corresponding to the 
    # three blocks of a QDIMACS file: header, quantifiers and clauses. 
    processing = Processing.HEADER

    lines = contents.splitlines(keepends=True)
    for line in lines:
        _current_line += 1

        # We will never have to worry about ignore = False with tokens = []; i.e., the case of line="" because of end of file.
        ignore, tokens = _is_comment(line)
        if ignore: continue

        
        if processing == Processing.HEADER:
            num_vars, num_clauses = _process_header_line_tokens(tokens)
            processing = Processing.QBLOCKS
            pre_q = ''

        elif processing == Processing.QBLOCKS:
            # Returned tokens only interesting when changing to state CLAUSES
            q, tokens = _process_quantifying_block_tokens(tokens, quantifiers, num_vars, pre_q)
            # First not quantifying line: end of the block
            if q is None:
                # Validate quantifiers before changing to the next state
                _validate_quantifiers(quantifiers, num_vars)    
                processing = Processing.CLAUSES
                # Do not forget the tokens corresponding to the non-quantifying line
                _process_clause_tokens(tokens, clauses, num_vars)
            else:
                pre_q = q
            
        elif processing == Processing.CLAUSES:
            _process_clause_tokens(tokens, clauses, num_vars)
        else:
            raise Exception("Incorrect processing state! This should never happen if the implementation is correct!")

    vars2clauses = _validate_clauses(clauses, num_vars, num_clauses)

    if simplify:
        num_vars, num_clauses, simplified = _simplify_formula(clauses, quantifiers, num_vars, num_clauses, vars2clauses)
        if simplified:
            name = _write_simplified_formula('simplified.qdimacs', num_vars, num_clauses, quantifiers, clauses)
            print("WARNING: The file contains a formula that has been simplified, without any need to "
                    "assign a value for any variable; i.e., repeated vars and clauses have been removed, "
                    "as well as tautological clauses (those that contain v and -v).\n\n"
                    f"Name of the new file: {name}")

    return num_vars, num_clauses, clauses, quantifiers

def read_qdimacs_from_file_unchecked(filepath: str) -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Version that assumes that the file is perfectly valid, so the parsing is done efficiently without almost any
    condition checking (the only unknown value is the number of comments prior to the header line).
    """
    clauses, quantifiers = [], []

    with open(filepath, 'r') as f:
        # Skip comments
        while True:
            tokens = f.readline().strip().split()
            if tokens[0] != 'c':
                break

        # Header line (contained in tokens)
        num_vars, num_clauses = map(int, tokens[2:])

        # Quantifier blocks
        tokens = f.readline().strip().split()

        # Special case of True literal
        if not tokens:
            return num_vars, num_clauses, clauses, quantifiers

        isDimacs = tokens[0] != 'a' and tokens[0] != 'e'
        if isDimacs:
            quantifiers.append(('e', list(range(1, num_vars + 1))))
        else:
            unquantified_vars = num_vars
            #while unquantified_vars:
            while tokens[0] == 'a' or tokens[0] == 'e':
                q, qvars = tokens[0], [int(t) for t in tokens[1:-1]]
                if qvars:
                    quantifiers.append((q, qvars))
                unquantified_vars -= len(qvars)
                tokens = f.readline().strip().split()

        # Clauses
        unread_clauses = num_clauses
        while True:
            if tokens:
                clauses.append([int(t) for t in tokens[:-1]])
            unread_clauses -= 1
            tokens = f.readline()
            if tokens == "":
                break
            tokens = tokens.strip().split()

    return num_vars, num_clauses, clauses, quantifiers

def read_qdimacs_from_str_unchecked(contents: str) -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Version that assumes that the contents are perfectly valid, so the parsing is done efficiently without almost any
    condition checking (the only unknown value is the number of comments prior to the header line).
    """
    clauses, quantifiers = [], []

    lines = contents.splitlines()
    i = 0
    
    # Skip comments
    while True:
        tokens = lines[i].strip().split()
        i += 1
        if tokens[0] != 'c':
            break

    # Header line (contained in tokens)
    num_vars, num_clauses = map(int, tokens[2:])
    
    # Quantifier blocks
    tokens = lines[i].strip().split()

    # Special case of True literal
    if not tokens:
        return num_vars, num_clauses, clauses, quantifiers

    i += 1
    isDimacs = tokens[0] != 'e' and tokens[0] != 'a'
    if isDimacs:
        quantifiers.append(('e', list(range(1, num_vars + 1))))
    else:
        unquantified_vars = num_vars
        while unquantified_vars:
            q, qvars = tokens[0], [int(t) for t in tokens[1:-1]]
            quantifiers.append((q, qvars))
            unquantified_vars -= len(qvars)
            tokens = lines[i].strip().split()
            i += 1

    # Clauses
    unread_clauses = num_clauses
    while unread_clauses:
        clauses.append([int(t) for t in tokens[:-1]])
        unread_clauses -= 1
        tokens = lines[i].strip().split()
        i += 1

    return num_vars, num_clauses, clauses, quantifiers

def read_qdimacs(f_or_c: str, simplify: bool = True, unchecked: bool = False) \
    -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Interface function to read QDIMACS formulas that decides automatically if the input is the file that contains the formulas
    or the content of the formula itself. Depending on that, it calls to read_qdimacs_from_file or read_qdimacs_from_str.

    Detail: if a file path is introduced, but the file does not exist, the str version of the DIMACS' parser is going to be
        called, and it will fail the check of the header line.
    """
    if os.path.isfile(f_or_c):
        if unchecked: return read_qdimacs_from_file_unchecked(f_or_c)
        return read_qdimacs_from_file(f_or_c, simplify)
    try:
        if unchecked: return read_qdimacs_from_str_unchecked(f_or_c)
        return read_qdimacs_from_str(f_or_c, simplify)
    except IncorrectFileFormatError:
        raise IncorrectFileFormatError('The file does not have the header file! Check if the file exists too.')
### QCIR #####################################################################################

def read_qcir_from_file(file_path: str, simplify: bool = True) \
    -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Function used to read a formula in a file with QCIR format. QCIR format is a much more flexible format than QDIMACS.
    It can express formulas in any form, not only in CNF or DNF like (Q)DIMACS. Therefore, to obtain the same structure
    as with QDIMACS, we use a conversor (Tseitin variables might be used) to obtain the equivalent CNF formula in QDIMACS
    format, and then use the parser that we have defined previously.

    Note: PySAT's 'formula' module has great class and interfaces that perfectly match the human-readable format of QCIR.
        A parser taking advantage of that could be implemented, and then use the clausify method of PySAT's Formula objects.
        Nonetheless, I guess that clausify uses the same procedure (Tseitin variables) to do the transformations. So both
        approximations are equivalent (assuming that qcir2qdimacs conversor is installed).

    Args:
        file_path (str): the path of the file in QCIR format
        simplify (bool): True by default. Indicates if simplifications are to be made to the QDIMACS parser.

    Returns:
        See the QDIMACS parser (read_qdimacs_from_str)

    Raises:
        See the QDIMACS parser (read_qdimacs_from_str)

    """
    qdimacs = subprocess.run(['qcir2qdimacs', file_path], capture_output=True, text=True).stdout
    return read_qdimacs_from_str(qdimacs, simplify)

def read_qcir_from_str(content: str, simplify: bool = True) -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Equivalent to read_qcir_from_file, but this version receives the contents in a string directly.
    """
    qdimacs = subprocess.run('qcir2qdimacs', capture_output=True, input=content, text=True).stdout
    return read_qdimacs_from_str(qdimacs, simplify)

def read_qcir_from_file_unchecked(file_path: str) -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Unchecked version.
    """
    qdimacs = subprocess.run(['qcir2qdimacs', file_path], capture_output=True, text=True).stdout
    return read_qdimacs_from_str_unchecked(qdimacs)

def read_qcir_from_str_unchecked(content: str) -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Unchecked version.
    """
    qdimacs = subprocess.run('qcir2qdimacs', capture_output=True, input=content, text=True).stdout
    return read_qdimacs_from_str_unchecked(qdimacs)

def read_qcir(f_or_c: str, simplify: bool = True, unchecked: bool = True) \
    -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Interface function to read QCIR formulas that decides automatically if the input is the file that contains the formulas
    or the content of the formula itself. Depending on that, it calls to read_qcir_from_file or read_qcir_from_str.

    Detail: if a file path is introduced, but the file does not exist, the str version of the QCIR's parser is going to be
        called, and it will fail the check of the header line.
    """
    if os.path.isfile(f_or_c):
        if unchecked: return read_qcir_from_file_unchecked(f_or_c)
        return read_qcir_from_file(f_or_c, simplify)
    try:
        if unchecked: return read_qcir_from_str_unchecked(f_or_c)
        return read_qcir_from_str(f_or_c, simplify)
    except IncorrectFileFormatError as e:
        raise IncorrectFileFormatError('The file does not have the header file! Check if the file exists too.')

### QAIGER ###################################################################################

def read_qaiger_from_file(file_path: str, simplify: bool = True) -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Function used to read a formula in a file with QAIGER format. QAIGER is similar to QCIR, it uses electric circuit concepts to 
    express formulas. Nonetheless, it is more limited. It does not have a way to express more advanced gates, as it primarily 
    focuses on AND gates. More importantly, it is way less readible than QCIR, and way more complicated than QDIMACS.

    Note: PySAT's 'formula' module has tools to read from files in AIGER format, but not QAIGER. Therefore, they can not be used,
        and that is why I use the conversor I have available to obtain the equivalent QDIMACS. As I do not have the conversor
        qaiger2qdimacs, I transform it first to QCIR and use the previously implemented functions for that format.

    Args:
        file_path (str): the path of the file in QCIR format
        simplify (bool): True by default. Indicates if simplifications are to be made to the QDIMACS parser.

    Returns:
        See the QDIMACS parser (read_qdimacs_from_str)

    Raises:
        See the QDIMACS parser (read_qdimacs_from_str)

    """
    qcir = subprocess.run(['qaiger2qcir', file_path], capture_output=True, text=True).stdout
    return read_qcir_from_str(qcir, simplify)

def read_qaiger_from_str(content: str, simplify: bool = True) -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Equivalent to read_qaiger_from_file, but this version receives the contents in a string directly.
    """
    qcir = subprocess.run('qaiger2qcir', capture_output=True, input=content, text=True).stdout
    return read_qcir_from_str(qcir, simplify)

def read_qaiger_from_file_unchecked(file_path: str) -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Unchecked version
    """
    qcir = subprocess.run(['qaiger2qcir', file_path], capture_output=True, text=True).stdout
    return read_qcir_from_str_unchecked(qcir)

def read_qaiger_from_str_unchecked(content: str) -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Unchecked version
    """
    qcir = subprocess.run('qaiger2qcir', capture_output=True, input=content, text=True).stdout
    return read_qcir_from_str_unchecked(qcir)

def read_qaiger(f_or_c: str, simplify: bool = True, unchecked: bool = True) \
    -> Tuple[PositiveInt, PositiveInt, CNF_Formula, List[QBlock]]:
    """
    Interface function to read QAIGER formulas that decides automatically if the input is the file that contains the formulas
    or the content of the formula itself. Depending on that, it calls to read_qaiger_from_file or read_qaiger_from_str.

    Detail: if a file path is introduced, but the file does not exist, the str version of the AIGER's parser is going to be
        called, and it will fail the check of the header line.
    """
    if os.path.isfile(f_or_c):
        if unchecked: return read_qaiger_from_file_unchecked(f_or_c)
        return read_qaiger_from_file(f_or_c, simplify)
    try:
        if unchecked: return read_qaiger_from_str_unchecked(f_or_c)
        return read_qaiger_from_str(f_or_c, simplify)
    except IncorrectFileFormatError as e:
        raise IncorrectFileFormatError('The file does not have the header file! Check if the file exists too.')