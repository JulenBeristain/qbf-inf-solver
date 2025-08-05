from pdb import set_trace
from types_qbf import *

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

def _unit_propagation(clauses: CNF_Formula, vars2quant: Dict[int, Quantifier]) -> None | bool:
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
    for clause in clauses:
        if all( vars2quant[abs(lit)] == 'a' for lit in clause ):
            return True
    return False

def _polarity(clauses: CNF_Formula, vars2quant: Dict[int, Quantifier]) -> None | bool:
    vars = list(vars2quant.keys())
    num_vars = len(vars)

    for v in range(1, num_vars):
        # polarities == ( [[i,j] where clauses[i,j] == v],  [[i',j'] where clauses[i',j'] == -v])
        polarities = ([], [])
        for i in range(len(clauses)):
            for j in range(len(clauses[i])):
                lit = clauses[i][j]
                assert lit != 0, "Ningún literal debería ser 0 !!!"
                if lit == v:
                    polarities[0].append([i,j])
                elif lit == -v:
                    polarities[1].append([i,j])
        
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
            for clause_i, lit_i in positions:
                clauses[clause_i].pop(lit_i)
                if not clauses[clause_i]:
                    return False


def preprocess(clauses: CNF_Formula, quantifiers: List[QBlock]) -> None | bool:
    vars2quant = {}
    for q, vars in quantifiers:
        for v in vars:
            vars2quant[v] = q

    if _check_empty_clause(clauses):
        return False
    _eliminate_tautological_variables(clauses)
    _eliminate_tautological_clauses(clauses)

    """
    Orden más apropiado de las simplificaciones:
    1. Polaridad: si una variable siempre aparece con la misma polaridad
        a) Es existencial, eliminamos las cláusulas donde aparece
        b) Es universal, eliminamos los literales (comprobando si queda una cláusula vacía -> False)
    2. Unit propagation con variables existenciales
        a) Eliminación de las cláusulas donde aparece el literal con la misma polaridad que en el 
           unit-clause (incluyendo el propio unit-clause)
        b) Eliminación de los literales con polaridad inversa en el resto de cláusulas (comprobando
           si queda alguna cláusula vacía -> False)
    3. Cláusulas con todo variables universales: si hay alguna cláusula compuesta únicamente por 
       variables universales -> False

    (3) no modifica las clásulas, sólo hace un chequeo. Por tanto, no simplifica la fórmula para que
    las demás transformaciones puedan simplificar todavía más la fórmula.

    (2) puede hacer que aparezcan más unit-clauses iterativamente, por lo que hay que ejecutarlo
    varias veces. También puede hacer que aparezcan cláusulas con variables universales al eliminar
    variables existenciales. Por tanto, conviene ejecutarlo antes de (3). Por otro lado, al detectar
    una variable de una unit-clause, se eliminan todas sus apariciones de la fórmula. Por tanto, si 
    dicha variable hubiera tenido la misma polaridad en toda la fórmula, la fórmula se simplifica de 
    la misma manera que con (1). No obstante, ejecutar primero (2) no ayuda a (1), ya que como elimina
    todas las apariciones de una variable y no sólo literales de una polaridad concreta de dicha variable,
    no genera variables que antes no tenían la misma polaridad y ahora sí.

    (1) puede coincider con (2) en el caso antes mencionado. Pero, en cuanto a las variables universales,
    puede hacer aparecer nuevos unit-clauses de variables existenciales, por lo que conviene ejecutarlo
    antes de (2). Por otro lado, si la variable existencial eliminada estuviera en una cláusula con otras
    variables universales (o sóla, dando como resultado False por cláusula vacía), la cláusula restante
    seguirá componiéndose únicamente por variables universales, por lo que (3) no es afectada.

    En conclusión, el orden para evitar varias llamadas iterativas a la misma simplificación sin perder
    por ello potenciales simplificaciones es 1-2-3, donde (2) sí que es iterativo sólo consigo mismo.
                                                   _
                                                  \ /
    Grafo de permitir siplificaciones extra:  1 -> 2 -> 3        
    """

    # In place modification to clauses
    if _polarity(clauses, vars2quant) is False:
        return False
    # In place modification to clauses
    if _unit_propagation(clauses, vars2quant) is False:
        return False
    
    if _any_all_universal_clause(clauses, vars2quant):
        return False