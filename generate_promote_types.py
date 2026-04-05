import numpy as np

# List of NumPy types to generate the matrix for
dtypes = [
    np.bool_,
    np.uint8, np.int8,
    np.uint16, np.int16,
    np.uint32, np.int32,
    np.uint64, np.int64,
    np.float16, np.float32, np.float64
]

with open('promote_types.pl', 'w') as f:
    f.write('% Generated NumPy type promotion matrix\n')
    f.write(':- module(promote_types, [numpy_promote/3]).\n\n')
    
    for t1 in dtypes:
        for t2 in dtypes:
            dt1 = np.dtype(t1).name
            dt2 = np.dtype(t2).name
            
            # Get the exact NumPy promotion result
            res = np.promote_types(t1, t2).name
            
            # Map bool to boolean if needed, but numpy stringifies it as 'bool'
            f.write(f'numpy_promote({dt1}, {dt2}, {res}).\n')
