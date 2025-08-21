# total_size.py

import sys
from typing import Any, Optional, Set

def get_total_size(obj: Any, seen: Optional[Set] = None) -> int:
    """
    Calculate the total size of an object and its nested elements recursively. 
    Avoid double-counting shared objects by using 'seen' (a set of IDs).

    Args:
        obj (Any): any Python object (everything in Python is an object), which may contain another nested ones.
        seen (Optional[Set]): the set of IDs (memory addresses in CPython) of the objects that were already detected in previous calls.

    Returns:
        int: the number of bytes that obj needs in memory.
    """
    if seen is None:
        seen = set()
    obj_id = id(obj)
    if obj_id in seen:
        return 0
    seen.add(obj_id)

    size = sys.getsizeof(obj)

    if isinstance(obj, dict):
        size += sum(get_total_size(k, seen) + get_total_size(v, seen) for k, v in obj.items())
    elif hasattr(obj, '__iter__') and not isinstance(obj, (str, bytes, bytearray)):
        size += sum(get_total_size(item, seen) for item in obj)
    elif hasattr(obj, '__dict__'): # For instances of user-defined classes
        size += get_total_size(obj.__dict__, seen) # Sum the dict of attributes
    return size