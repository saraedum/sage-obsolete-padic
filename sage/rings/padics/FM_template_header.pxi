

include "padic_template_element_header.pxi"

from sage.categories.morphism cimport Morphism
from sage.rings.morphism cimport RingHomomorphism_coercion, RingMap

cdef class FMElement(pAdicTemplateElement):
    cdef celement value
    cdef long absprec

    cdef FMElement _new_c(self)

cdef class pAdicCoercion_ZZ_FM(RingHomomorphism_coercion):
    cdef FMElement _zero
    cdef RingMap _section
cdef class pAdicConvert_FM_ZZ(RingMap):
    pass
cdef class pAdicConvert_QQ_FM(Morphism):
    cdef FMElement _zero
    cdef RingMap _section
