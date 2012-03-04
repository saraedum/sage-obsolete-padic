

include "padic_template_element_header.pxi"

from sage.categories.morphism cimport Morphism
from sage.rings.morphism cimport RingHomomorphism_coercion, RingMap

cdef class CRElement(pAdicTemplateElement):
    cdef celement unit
    cdef long ordp
    cdef long relprec

    cdef CRElement _new_c(self)
    cdef int _normalize(self) except -1

cdef class pAdicCoercion_ZZ_CR(RingHomomorphism_coercion):
    cdef CRElement _zero
    cdef RingMap _section
cdef class pAdicConvert_CR_ZZ(RingMap):
    pass
cdef class pAdicCoercion_QQ_CR(RingHomomorphism_coercion):
    cdef CRElement _zero
    cdef RingMap _section
cdef class pAdicConvert_CR_QQ(RingMap):
    pass
cdef class pAdicConvert_QQ_CR(Morphism):
    cdef CRElement _zero
    cdef RingMap _section
