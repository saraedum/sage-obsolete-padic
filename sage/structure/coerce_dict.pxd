cdef class TripleDict:
    cdef Py_ssize_t _size
    cdef buckets
    cdef double threshold
    cdef TripleDictEraser eraser
    cdef get(self, object k1, object k2, object k3)
    cdef set(self, object k1, object k2, object k3, value)
    
cdef class TripleDictIter:
    cdef TripleDict pairs
    cdef buckets, bucket_iter

cdef class TripleDictEraser:
    cdef TripleDict D
