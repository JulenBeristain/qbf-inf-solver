import sys
from compactify import C_CNF_Tree

def get_total_size(obj, seen=None):
    """
    Calcula el tamaño total de un objeto y sus elementos anidados de forma recursiva.
    Evita la doble cuenta de objetos compartidos mediante 'seen' (conjunto de IDs).
    """
    if seen is None:
        seen = set()
    obj_id = id(obj)
    if obj_id in seen:
        return 0  # Ya contamos este objeto
    seen.add(obj_id)

    size = sys.getsizeof(obj)

    if isinstance(obj, dict):
        size += sum(get_total_size(k, seen) + get_total_size(v, seen) for k, v in obj.items())
    elif hasattr(obj, '__iter__') and not isinstance(obj, (str, bytes, bytearray)):
        # Si es iterable (no string/bytes para evitar iterar caracteres/bytes)
        size += sum(get_total_size(item, seen) for item in obj)
    elif hasattr(obj, '__dict__'): # Para instancias de clases personalizadas
        size += get_total_size(obj.__dict__, seen) # Sumar el diccionario de atributos
    # Puedes añadir más condiciones para otros tipos específicos si es necesario
    elif isinstance(obj, C_CNF_Tree_Slotted):
        size += get_total_size(obj.v, seen)
        size += get_total_size(obj.negative, seen)
        size += get_total_size(obj.positive, seen)
        size += get_total_size(obj.absent, seen)
    
    return size

class C_CNF_Tree_Slotted:
    __slots__ = ("v", "negative", "positive", "absent")

    def __init__(self, v, neg, pos, abs):
        self.v = v
        self.negative = neg
        self.positive = pos
        self.absent = abs

def test_node_sizes():
    true1 = C_CNF_Tree(True, None, None, None)
    true2 = C_CNF_Tree_Slotted(True, None, None, None)
    true3 = True
    true4 = True
    print(f"True 1 = {get_total_size(true1)}")
    print(f"True 2 = {get_total_size(true2)}")
    print(f"True 3 = {get_total_size(true3)}")
    print(f"True 4 = {get_total_size(true4)}")

    false1 = C_CNF_Tree(False, None, None, None)
    false2 = C_CNF_Tree(False, None, None, None)
    false3 = False
    false4 = False
    print(f"False 1 = {get_total_size(false1)}")
    print(f"False 2 = {get_total_size(false2)}")
    print(f"False 3 = {get_total_size(false3)}")
    print(f"False 4 = {get_total_size(false4)}")

    x11 = C_CNF_Tree(1, true1, false1, true1)
    x12 = C_CNF_Tree_Slotted(1, true2, false2, true2)
    x13 = [1, True, False, True]
    x14 = (1, True, False, True)
    print(f"x1 1 = {get_total_size(x11)}")
    print(f"x1 2 = {get_total_size(x12)}")
    print(f"x1 3 = {get_total_size(x13)}")
    print(f"x1 4 = {get_total_size(x14)}")

    # x2 or x1
    phi1 = C_CNF_Tree(2, true1, x11, true1)
    phi2 = C_CNF_Tree_Slotted(2, true2, x12, true2)
    phi3 = [2, True, x13, True]
    phi4 = (2, True, x14, True)
    print(f"x2 or x1 1 = {get_total_size(phi1)}")
    print(f"x2 or x1 2 = {get_total_size(phi2)}")
    print(f"x2 or x1 3 = {get_total_size(phi3)}")
    print(f"x2 or x1 4 = {get_total_size(phi4)}")

if __name__ == "__main__":
    test_node_sizes()
