# Thread caps for every BLAS backend, set before torch is imported. NNC_THREADS overrides.
import os as _os
for _v in ('OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS', 'OPENBLAS_NUM_THREADS'):
    _os.environ.setdefault(_v, _os.environ.get('NNC_THREADS', '2'))
