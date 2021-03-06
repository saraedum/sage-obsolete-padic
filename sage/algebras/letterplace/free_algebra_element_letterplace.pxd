###############################################################################
#
#       Copyright (C) 2011 Simon King <simon.king@uni-jena.de>
#  Distributed under the terms of the GNU General Public License (GPL),
#  version 2 or any later version.  The full text of the GPL is available at:
#                  http://www.gnu.org/licenses/
#
###############################################################################

cdef class FreeAlgebraElement_letterplace

from sage.structure.element cimport AlgebraElement, ModuleElement, RingElement, Element
from sage.rings.polynomial.multi_polynomial_libsingular cimport MPolynomialRing_libsingular, MPolynomial_libsingular
from sage.algebras.letterplace.free_algebra_letterplace cimport FreeAlgebra_letterplace
include "../../ext/stdsage.pxi"

cdef class FreeAlgebraElement_letterplace(AlgebraElement):
    cdef MPolynomial_libsingular _poly

