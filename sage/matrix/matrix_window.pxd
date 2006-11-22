from matrix cimport Matrix

cdef class MatrixWindow:
    cdef Py_ssize_t _row, _col, _nrows, _ncols
    cdef Matrix _matrix
    cdef object _zero

    # YOU *MUST* OVERRIDE THESE
    # Derived classes *MUST* implement _new_matrix_window. 
    cdef MatrixWindow new_matrix_window(MatrixWindow self, Matrix matrix, 
                                        Py_ssize_t row, Py_ssize_t col, Py_ssize_t n_rows, Py_ssize_t n_cols)

    # YOU *REALLY SHOULD* OVERRIDE THESE:
    cdef add(MatrixWindow self, MatrixWindow A)
    cdef subtract(MatrixWindow self, MatrixWindow A)
    cdef set_to_sum(MatrixWindow self, MatrixWindow A, MatrixWindow B)
    cdef set_to_diff(MatrixWindow self, MatrixWindow A, MatrixWindow B)
    cdef set_to_prod(MatrixWindow self, MatrixWindow A, MatrixWindow B)
    cdef add_prod(MatrixWindow self, MatrixWindow A, MatrixWindow B) 
    cdef subtract_prod(MatrixWindow self, MatrixWindow A, MatrixWindow B)
    
    cdef int element_is_zero(MatrixWindow self, Py_ssize_t i, Py_ssize_t j)
    cdef set_to(MatrixWindow self, MatrixWindow A) 
    cdef set_to_zero(MatrixWindow self)

    # FOR BETTER SPEED, OVERRIDE ANY SUBSET OF THESE (OPTIONAL):
    cdef set_unsafe(self, Py_ssize_t i, Py_ssize_t j, x)
    cdef get_unsafe(self, Py_ssize_t i, Py_ssize_t j)
    cdef to_matrix(MatrixWindow self)
    cdef new_empty_window(MatrixWindow self, Py_ssize_t nrows, Py_ssize_t ncols)
    
    # NO BENEFIT TO OVERRIDING THESE:
    cdef MatrixWindow matrix_window(MatrixWindow self, Py_ssize_t row, Py_ssize_t col,
                                    Py_ssize_t n_rows, Py_ssize_t n_cols)
    cdef matrix(MatrixWindow self)
    cdef swap_rows(MatrixWindow self, Py_ssize_t a, Py_ssize_t b)


            
