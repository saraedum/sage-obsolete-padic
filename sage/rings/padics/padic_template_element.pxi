"""
This file gives a class from which all the p-adic templates inherit.

This file is included in the various precision template files (such as sage/rings/padics/CR_template.pxi).
While this choice means that routines here do have access to the inlined functions defined in the linkage files,
the downside is that there will be multiple pAdicTemplateElement classes, one for each p-adic template.

AUTHORS:

- David Roe -- initial version (2012-3-1)
"""

#*****************************************************************************
#       Copyright (C) 2007-2013 David Roe <roed.math@gmail.com>
#                               William Stein <wstein@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************

include "../../libs/pari/decl.pxi"

import sage.rings.finite_rings.integer_mod
from sage.libs.pari.gen cimport gen as pari_gen
cdef extern from "convert.h":
    cdef void t_INT_to_ZZ( mpz_t value, GEN g )
from sage.rings.padics.common_conversion cimport get_ordp, get_preccap
from sage.rings.integer cimport Integer
from sage.rings.infinity import infinity
from sage.rings.rational import Rational
from sage.rings.padics.precision_error import PrecisionError

#cdef inline long min(long a, long b):
#    if a < b:
#        return a
#    return b

cdef long maxordp = (1L << (sizeof(long) * 8 - 2)) - 1
cdef long minusmaxordp = -maxordp

cdef inline int check_ordp(long ordp) except -1:
    """
    Checks for overflow after addition or subtraction of valuations.

    There is another variant, :meth:`check_ordp_mpz`, for ``mpz_t`` input.

    If overflow is detected, raises a ValueError.
    """
    if ordp >= maxordp or ordp <= minusmaxordp:
        raise ValueError, "valuation overflow"

cdef class pAdicTemplateElement(pAdicGenericElement):
    """
    A class for common functionality among the p-adic template classes.

    INPUT:

    - ``parent`` -- a local ring or field

    - ``x`` -- data defining this element.  Various types are supported,
      including ints, Integers, Rationals, PARI p-adics, integers mod `p^k`
      and other Sage p-adics.

    - ``absprec`` -- a cap on the absolute precision of this element

    - ``relprec`` -- a cap on the relative precision of this element

    EXAMPLES::

        sage: Zp(17)(17^3, 8, 4)
        17^3 + O(17^7)
    """
    def __init__(self, parent, x, absprec=infinity, relprec=infinity):
        """
        Initialization.

        EXAMPLES::

            sage: a = Zp(5)(1/2,3); a
            3 + 2*5 + 2*5^2 + O(5^3)
            sage: type(a)
            
            sage: TestSuite(a).run()
        """
        self.prime_pow = <PowComputer_class?>parent.prime_pow
        pAdicGenericElement.__init__(self, parent)
        cdef long val, xprec
        cdef GEN pari_tmp
        if isinstance(x, (int, long)):
            x = Integer(x)
        elif PY_TYPE_CHECK(x, pari_gen):
            pari_tmp = (<pari_gen>x).g
            if typ(pari_tmp) == t_INT:
                x = PY_NEW(Integer)
                t_INT_to_ZZ((<Integer>x).value, pari_tmp)
            elif typ(pari_tmp) == t_FRAC:
                x = Rational(x)
        elif not (PY_TYPE_CHECK(x, Integer) or \
                  PY_TYPE_CHECK(x, Rational) or \
                  PY_TYPE_CHECK(x, pAdicGenericElement) or \
                  PY_TYPE_CHECK(x, pari_gen) or \
                  sage.rings.finite_rings.integer_mod.is_IntegerMod(x)):
            x = Rational(x)
        val = get_ordp(x, self.prime_pow)
        if val < 0 and self.prime_pow.in_field == 0:
            raise ValueError("negative valuation")
        xprec = get_preccap(x, self.prime_pow)
        self._set(x, val, xprec, absprec, relprec)

    cdef int _set(self, x, long val, long xprec, absprec, relprec) except -1:
        """
        Sets this element from given data computed in :meth:`__init__`

        INPUT:

        - ``x`` -- an int, Integer, Rational, PARI p-adic, integer mod `p^k` or Sage p-adic
        - ``val`` -- a long, the valuation of ``x``
        - ``xprec`` -- a long, the cap on the absolute precision imposed by ``x``
        - ``absprec`` -- an integer or infinity, a bound on the absolute precision
        - ``relprec`` -- an integer or infinity, a bound on the relative precision
        """
        raise NotImplementedError

    def __lshift__(pAdicTemplateElement self, shift):
        """
        Multiplies ``self`` by ``pi^shift``.

        If ``shift`` is negative and this element does not lie in a field,
        digits may be truncated.  See ``__rshift__`` for details.
        
        EXAMPLES:
        
        We create some `p`-adic rings::
        
            sage: R = Zp(5, 20, 'capped-abs'); a = R(1000); a
            3*5^3 + 5^4 + O(5^20)
            sage: S = Zp(5); b = S(1000); b
            3*5^3 + 5^4 + O(5^23)

        Shifting to the right is the same as dividing by a power of
        the uniformizer `p` of the `p`-adic ring.::
        
            sage: a >> 1
            3*5^2 + 5^3 + O(5^19)
            sage: b >> 1
            3*5^2 + 5^3 + O(5^22)

        Shifting to the left is the same as multiplying by a power of
        `p`::
        
            sage: a << 2
            3*5^5 + 5^6 + O(5^20)
            sage: a*5^2
            3*5^5 + 5^6 + O(5^20)
            sage: b << 2
            3*5^5 + 5^6 + O(5^25)
            sage: b*5^2
            3*5^5 + 5^6 + O(5^25)

        Shifting by a negative integer to the left is the same as
        right shifting by the absolute value::

            sage: a << -3
            3 + 5 + O(5^17)
            sage: a >> 3
            3 + 5 + O(5^17)
            sage: b << -3
            3 + 5 + O(5^20)
            sage: b >> 3
            3 + 5 + O(5^20)
        """
        # TODO: move this up the hierarchy, perhaps this should go all the way to element?
        # The "verify that shift is an integer" part could be shared
        cdef long s
        if PyInt_Check(shift):
            s = PyInt_AS_LONG(shift)
        else:
            if not PY_TYPE_CHECK(shift, Integer):
                shift = Integer(shift)
            if mpz_fits_slong_p((<Integer>shift).value) == 0:
                raise ValueError("valuation overflow")
            s = mpz_get_si((<Integer>shift).value)
        check_ordp(s)
        return self._lshift_c(s)

    cdef pAdicTemplateElement _lshift_c(self, long shift):
        raise NotImplementedError

    def __rshift__(pAdicTemplateElement self, shift):
        """
        Divides by ``p^shift``, and truncates (if the parent is not a field).
        
        EXAMPLES::
        
            sage: R = Zp(997, 7, 'capped-abs'); a = R(123456878908); a
            964*997 + 572*997^2 + 124*997^3 + O(997^7)
            sage: S = Zp(5); K = Qp(5); b = S(17); b
            2 + 3*5 + O(5^20)

        Shifting to the right divides by a power of `p`, but drops
        terms with negative valuation::
            
            sage: a >> 3
            124 + O(997^4)
            sage: b >> 1
            3 + O(5^19)
            sage: b >> 40
            O(5^0)

        If the parent is a field no truncation is performed::

            sage: K(17) >> 1
            2*5^-1 + 3 + O(5^19)

        A negative shift multiplies by that power of `p`::
        
            sage: a >> -3
            964*997^4 + 572*997^5 + 124*997^6 + O(997^7)
            sage: K(17) >> -5
            2*5^5 + 3*5^6 + O(5^25)
        """
        cdef long s
        if PyInt_Check(shift):
            s = PyInt_AS_LONG(shift)
        else:
            if not PY_TYPE_CHECK(shift, Integer):
                shift = Integer(shift)
            if mpz_fits_slong_p((<Integer>shift).value) == 0:
                raise ValueError, "valuation overflow"
            s = mpz_get_si((<Integer>shift).value)
        check_ordp(s)
        return self._rshift_c(s)

    cdef pAdicTemplateElement _rshift_c(self, long shift):
        """
        Divides by ``p^shift`` and truncates (if the parent is not a field).
        """
        raise NotImplementedError

    cdef int check_preccap(self) except -1:
        """
        Checks that this element doesn't have precision higher than allowed by the precision cap.
        """
        raise NotImplementedError

    def lift_to_precision(self, absprec):
        """
        Returns another element of the same parent with absolute precision at least ``absprec``, 
        congruent to this `p`-adic element modulo the precision of this element.

        If such lifting would yield an element with precision greater
        than allowed by the precision cap of ``self``'s parent, an
        error is raised (though not for fixed modulus precision handling).
        
        EXAMPLES::
        
            sage: R = ZpCA(17)
            sage: R(-1,2).lift_to_precision(10)
            16 + 16*17 + O(17^10)
            sage: R(1,15).lift_to_precision(10)
            1 + O(17^15)
            sage: R(1,15).lift_to_precision(30)
            Traceback (most recent call last):
            ...
            PrecisionError: Precision higher than allowed by the precision cap.

            sage: R = Zp(5); c = R(17,3); c.lift_to_precision(8)
            2 + 3*5 + O(5^8)

        Fixed modulus elements don't raise errors::

            sage: R = ZpFM(5); a = R(5); a.lift_to_precision(7)
            5 + O(5^20)
            sage: a.lift_to_precision(10000)
            5 + O(5^20)
        """
        if not PY_TYPE_CHECK(absprec, Integer):
            absprec = Integer(absprec)
        if mpz_fits_slong_p((<Integer>absprec).value) == 0:
            raise PrecisionError("Precision higher than allowed by the precision cap")
        ans = self.lift_to_precision_c(mpz_get_si((<Integer>absprec).value))
        ans.check_preccap()
        return ans

    cdef pAdicTemplateElement lift_to_precision_c(self, long absprec):
        """
        Lifts this element to another with precision at least absprec.
        """
        raise NotImplementedError

    def padded_list(self, n, lift_mode = 'simple'):
        """
        Returns a list of coefficients of the uniformizer `\pi`
        starting with `\pi^0` up to `\pi^n` exclusive (padded with
        zeros if needed).

        For a field element of valuation `v`, starts at `\pi^v`
        instead.

        INPUT:

        - ``n`` - an integer

        - ``lift_mode`` - 'simple', 'smallest' or 'teichmuller'

        EXAMPLES::

            sage: R = Zp(7,4,'capped-abs'); a = R(2*7+7**2); a.padded_list(5)
            [0, 2, 1, 0, 0]
            sage: R = Zp(7,4,'fixed-mod'); a = R(2*7+7**2); a.padded_list(5)
            [0, 2, 1, 0, 0]

        For elements with positive valuation, this function will
        return a list with leading 0s if the parent is not a field::

            sage: R = Zp(7,3,'capped-rel'); a = R(2*7+7**2); a.padded_list(5)
            [0, 2, 1, 0, 0]
            sage: R = Qp(7,3); a = R(2*7+7**2); a.padded_list(5)
            [2, 1, 0, 0]
            sage: a.padded_list(3)
            [2, 1]
        """
        if lift_mode == 'simple' or lift_mode == 'smallest':
            # needs to be defined in the linkage file.
            zero = _list_zero
        elif lift_mode == 'teichmuller':
            zero = self.parent()(0,0)
        else:
            raise ValueError("%s not a recognized lift mode"%lift_mode)
        L = self.list(lift_mode)
        if self.prime_pow.in_field == 1:
            if self._is_exact_zero():
                n = 0
            else:
                n -= self.valuation()
        return L[:n] + [zero] * (n - len(L))

    cpdef pAdicTemplateElement unit_part(self):
        """
        Returns the unit part of this element.

        This is the `p`-adic element `u` in the same ring so that this
        element is `\pi^v u`, where `\pi` is a uniformizer and `v` is
        the valuation of this element.
        """
        raise NotImplementedError

    cpdef bint _is_base_elt(self, p) except -1:
        """
        Returns True if this element is an element of Zp or Qp (rather than an extension).

        INPUT:

        - ``p`` -- a prime, which is compared with the parent of this element.

        EXAMPLES::

            sage: a = Zp(5)(3); a._is_base_elt(5)
            True
            sage: a._is_base_elt(17)
            False
        """
        return self.prime_pow.prime == p and self.prime_pow.deg == 1

cdef Integer pow_helper(long *ansrelprec, long *exp_prec, long ordp, long relprec, _right, PowComputer_class prime_pow):
    """
    This function is used by exponentiation in both CR_template.pxi
    and CA_template.pxi to determine the extra precision gained from
    an exponent of positive valuation.  See __pow__ there and in
    padic_ZZ_pX_CR_element.pyx for more details on this phenomenon.

    INPUT:

    - ansrelprec -- (return value) the relative precision of the answer

    - exp_prec -- (return value) a nonnegative integer, or -1 to indicate infinite precision exponent

    - ordp -- an integer: just used to check that the base is a unit for p-adic exponents

    - relprec -- a positive integer: the relative precision of the base

    - _right -- the exponent, nonzero

    - prime_pow -- the Powcomputer for the ring.

    OUTPUT:

    - an Integer congruent to the given exponent
    """
    ####### NOTE:  this function needs to be updated for extension elements. #######
    cdef Integer right, p = prime_pow.prime
    cdef long exp_val
    cdef bint isbase
    if isinstance(_right, (int, long)):
        _right = Integer(_right)
    if PY_TYPE_CHECK(_right, Integer):
        right = <Integer> _right
        exp_val = mpz_get_si((<Integer>right.valuation(p)).value)
        exp_prec[0] = -1
    elif PY_TYPE_CHECK(_right, Rational):
        raise NotImplementedError
    else:
        try:
            isbase = _right._is_base_elt(p)
        except AttributeError:
            isbase = False
        if not isbase:
            raise TypeError("exponent must be an integer, rational or base p-adic with the same prime")
        if ordp != 0:
            raise ValueError("in order to raise to a p-adic exponent, base must be a unit")
        right = Integer(_right)
        exp_prec[0] = mpz_get_si((<Integer>_right.precision_absolute()).value)
        exp_val = (<pAdicGenericElement>_right).valuation_c()
        if exp_val < 0:
            raise NotImplementedError("negative valuation exponents not yet supported")
        if exp_prec[0] == 0:
            # The calling code should set an inexact zero with no precision
            return right
    ansrelprec[0] = relprec + exp_val
    if exp_val > 0 and mpz_cmp_ui(p.value, 2) == 0 and relprec == 1:
        ansrelprec[0] += 1
    
    return right

cdef inline long padic_exp_helper(long relprec, long exp_prec, long base_level, PowComputer_class prime_pow) except -1:
    """
    Used by CR_template.pxi and CA_template.pxi in computing the
    precision of exponentiation when the exponent is itself a `p`-adic
    number.

    INPUT:

    - ``relprec`` -- (positive integer) the relative precision bound
      produced by ``pow_helper``

    - ``exp_prec`` -- (positive integer) the precision of the `p`-adic
      exponent.

    - ``base_level`` -- (positive integer) the valuation of
      `u/teich(u) - 1`, where `u` is the unit part of the base.

    - ``prime_pow`` -- the Powcomputer for the ring.

    OUTPUT:

    - an updated relative precision for the result.
    """
    if base_level == 0:
        raise ValueError("in order to raise to a p-adic exponent, base must reduce to an element of F_p mod the uniformizer")
    cdef Integer p = prime_pow.prime
    if mpz_cmp_ui(p.value, 2) == 0 and base_level == 1:
        base_level = 2
    return min(relprec, base_level + exp_prec)
