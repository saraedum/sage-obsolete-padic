

# The downside of using a .pxi file here is that there will be multiple pAdicTemplateElement classes: you can't
# cimport a common pAdicTemplateElement.

from sage.structure.element cimport ModuleElement, RingElement
from sage.rings.padics.padic_generic_element cimport pAdicGenericElement
from sage.rings.padics.pow_computer cimport PowComputer_class

cdef class pAdicTemplateElement(pAdicGenericElement):
    cdef PowComputer_class prime_pow
    cdef int _set(self, x, long val, long xprec, absprec, relprec) except -1
    cdef pAdicTemplateElement _lshift_c(self, long shift)
    cdef pAdicTemplateElement _rshift_c(self, long shift)
    #cpdef RingElement _floordiv_c_impl(self, RingElement right)
    cdef int check_preccap(self) except -1
    cdef pAdicTemplateElement lift_to_precision_c(self, long absprec)
    cpdef pAdicTemplateElement unit_part(self)
