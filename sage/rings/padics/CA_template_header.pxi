

include "padic_template_element_header.pxi"

from sage.categories.morphism cimport Morphism
from sage.rings.morphism cimport RingHomomorphism_coercion, RingMap

cdef class CAElement(pAdicTemplateElement):
    cdef celement value
    cdef long absprec

    cdef CAElement _new_c(self)

cdef class pAdicCoercion_ZZ_CA(RingHomomorphism_coercion):
    cdef CAElement _zero
    cdef RingMap _section
cdef class pAdicConvert_CA_ZZ(RingMap):
    pass
cdef class pAdicConvert_QQ_CA(Morphism):
    cdef CAElement _zero
    cdef RingMap _section
# There should also be a pAdicConvert_CA_QQ for extension rings....
