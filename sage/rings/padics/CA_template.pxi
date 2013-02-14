"""
Capped absolute template for complete discrete valuation rings.

In order to use this template you need to write a linkage file and gluing file.
For an example see mpz_linkage.pxi (linkage file) and padic_capped_absolute_element.pyx (gluing file).

The linkage file implements a common API that is then used in the class CAElement defined here.
See the documentation of mpz_linkage.pxi for the functions needed.

The gluing file does the following:

- includes "../../ext/cdefs.pxi"
- ctypedef's celement to be the appropriate type (e.g. mpz_t)
- includes the linkage file
- includes this template
- defines a concrete class inheriting from CRElement, and implements any desired extra methods

AUTHORS:

- David Roe (2012-3-1) -- initial version
"""

#*****************************************************************************
#       Copyright (C) 2012 David Roe <roed.math@gmail.com>
#                          William Stein <wstein@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************

# This file implements common functionality among template elements
include "padic_template_element.pxi"

from sage.structure.element cimport Element
from sage.rings.padics.common_conversion cimport comb_prec, _process_args_and_kwds
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.categories.sets_cat import Sets
from sage.categories.sets_with_partial_maps import SetsWithPartialMaps
from sage.categories.homset import Hom

cdef class CAElement(pAdicTemplateElement):
    cdef int _set(self, x, long val, long xprec, absprec, relprec) except -1:
        """
        TESTS::

            sage: R = ZpCA(5)
            sage: a = R(17,5); a #indirect doctest
            2 + 3*5 + O(5^5)
            sage: a = R(75, absprec = 5, relprec = 4); a #indirect doctest
            3*5^2 + O(5^5)
            sage: a = R(25/9, absprec = 5); a #indirect doctest
            4*5^2 + 2*5^3 + O(5^5)
            sage: a = R(25/9, absprec = 5, relprec = 4); a #indirect doctest
            4*5^2 + 2*5^3 + O(5^5)
        """
        cconstruct(self.value, self.prime_pow)
        cdef long rprec = comb_prec(relprec, self.prime_pow.prec_cap)
        cdef long aprec = comb_prec(absprec, min(self.prime_pow.prec_cap, xprec))
        if aprec <= val:
            csetzero(self.value, self.prime_pow)
            self.absprec = aprec
        else:
            self.absprec = min(aprec, val + rprec)
            cconv(self.value, x, self.absprec, 0, self.prime_pow)

    cdef CAElement _new_c(self):
        """
        Creates a new element with the same basic info.

        TESTS::

            sage: R = ZpCA(5); R(6,5) * R(7,8) #indirect doctest
            2 + 3*5 + 5^2 + O(5^5)
        """
        cdef CAElement ans = PY_NEW(self.__class__)
        ans._parent = self._parent
        ans.prime_pow = self.prime_pow
        cconstruct(ans.value, ans.prime_pow)
        return ans

    cdef int check_preccap(self) except -1:
        """
        Checks that this element doesn't have precision higher than allowed by the precision cap.

        TESTS::

            sage: ZpCA(5)(1).lift_to_precision(30)
            Traceback (most recent call last):
            ...
            PrecisionError: Precision higher than allowed by the precision cap.
        """
        if self.absprec > self.prime_pow.prec_cap:
            raise PrecisionError("Precision higher than allowed by the precision cap.")

    def __copy__(self):
        """
        Returns a copy of ``self``.

        EXAMPLES::

            sage: a = ZpCA(5,6)(17); b = copy(a)
            sage: a == b
            True
            sage: a is b
            False
        """
        cdef CAElement ans = self._new_c()
        ans.absprec = self.absprec
        ccopy(ans.value, self.value, ans.prime_pow)
        return ans

    def __dealloc__(self):
        """
        Deallocation.

        TESTS::

            sage: R = ZpCA(5)
            sage: a = R(17)
            sage: del(a)
        """
        cdestruct(self.value, self.prime_pow)

    def __reduce__(self):
        """
        Pickling.

        TESTS::
        
            sage: a = ZpCA(5)(-3)
            sage: type(a)
            <type 'sage.rings.padics.padic_capped_absolute_element.pAdicCappedAbsoluteElement'>
            sage: loads(dumps(a)) == a
            True
        """
        return unpickle_cae_v2, (self.__class__, self.parent(), cpickle(self.value, self.prime_pow), self.absprec)

    def __richcmp__(self, right, int op):
        """
        Comparison.

        TESTS::

            sage: R = ZpCA(5)
            sage: a = R(17)
            sage: b = R(21)
            sage: a == b
            False
            sage: a < b
            True
        """
        return (<Element>self)._richcmp(right, op)

    cpdef ModuleElement _neg_(self):
        """
        Returns the negation of self.

        EXAMPLES::
        
            sage: R = Zp(5, prec=10, type='capped-abs')
            sage: a = R(1)
            sage: -a #indirect doctest
            4 + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + 4*5^5 + 4*5^6 + 4*5^7 + 4*5^8 + 4*5^9 + O(5^10)
        """
        cdef CAElement ans = self._new_c()
        ans.absprec = self.absprec
        cneg(ans.value, self.value, ans.absprec, ans.prime_pow)
        creduce_small(ans.value, ans.value, ans.absprec, ans.prime_pow)
        return ans

    cpdef ModuleElement _add_(self, ModuleElement _right):
        """
        Addition.
        
        EXAMPLES::
        
            sage: R = ZpCA(13, 4)
            sage: R(2) + R(3) #indirect doctest
            5 + O(13^4)
            sage: R(12) + R(1)
            13 + O(13^4)
        """
        cdef CAElement right = <CAElement>_right
        cdef CAElement ans = self._new_c()
        ans.absprec = min(self.absprec, right.absprec)
        cadd(ans.value, self.value, right.value, ans.absprec, ans.prime_pow)
        creduce_small(ans.value, ans.value, ans.absprec, ans.prime_pow)
        return ans

    cpdef ModuleElement _sub_(self, ModuleElement _right):
        """
        Subtraction.
        
        EXAMPLES::
        
            sage: R = ZpCA(13, 4)
            sage: R(10) - R(10) #indirect doctest
            O(13^4)
            sage: R(10) - R(11)
            12 + 12*13 + 12*13^2 + 12*13^3 + O(13^4)
        """
        cdef CAElement right = <CAElement>_right
        cdef CAElement ans = self._new_c()
        ans.absprec = min(self.absprec, right.absprec)
        csub(ans.value, self.value, right.value, ans.absprec, ans.prime_pow)
        creduce_small(ans.value, ans.value, ans.absprec, ans.prime_pow)
        return ans

    def __invert__(self):
        """
        Returns the multiplicative inverse of ``self``.
        
        EXAMPLES::
        
            sage: R = ZpCA(17)
            sage: ~R(-1) == R(-1)
            True
            sage: ~R(5) * 5
            1 + O(17^20)
            sage: ~R(5)
            7 + 3*17 + 10*17^2 + 13*17^3 + 6*17^4 + 3*17^5 + 10*17^6 + 13*17^7 + 6*17^8 + 3*17^9 + 10*17^10 + 13*17^11 + 6*17^12 + 3*17^13 + 10*17^14 + 13*17^15 + 6*17^16 + 3*17^17 + 10*17^18 + 13*17^19 + O(17^20)
            sage: ~R(-1) == R(-1) #indirect doctest
            True
        """
        return self.parent().fraction_field()(self).__invert__()

    cpdef RingElement _mul_(self, RingElement _right):
        """
        Multiplication.
        
        EXAMPLES::
        
            sage: R = ZpCA(5)
            sage: a = R(20,5); b = R(75, 4); a * b #indirect doctest
            2*5^3 + 2*5^4 + O(5^5)
        """
        cdef CAElement right = <CAElement>_right        
        cdef CAElement ans = self._new_c()
        cdef long vals, valr
        if self.absprec == self.prime_pow.prec_cap and right.absprec == self.prime_pow.prec_cap:
            ans.absprec = self.absprec
        else:
            vals = self.valuation_c()
            valr = right.valuation_c()
            ans.absprec = min(vals + valr + min(self.absprec - vals, right.absprec - valr), self.prime_pow.prec_cap)
        cmul(ans.value, self.value, right.value, ans.absprec, ans.prime_pow)
        creduce(ans.value, ans.value, ans.absprec, ans.prime_pow)
        return ans

    cpdef RingElement _div_(self, RingElement right):
        """
        Division.

        EXAMPLES::

            sage: R = ZpCA(13, 4)
            sage: R(2) / R(3) # indirect doctest
            5 + 4*13 + 4*13^2 + 4*13^3 + O(13^4)
            sage: a = R(169 * 2) / R(13); a
            2*13 + O(13^3)
            sage: R(13) / R(169 * 2)
            7*13^-1 + 6 + O(13)
            sage: ~a
            7*13^-1 + 6 + O(13)
            sage: 1 / a
            7*13^-1 + 6 + O(13)
        """
        K = self.parent().fraction_field()
        return K(self) / K(right)

    def __pow__(CAElement self, _right, dummy):
        """
        Exponentiation.
        
        EXAMPLES::
        
            sage: R = ZpCA(11, 5)
            sage: R(1/2)^5
            10 + 7*11 + 11^2 + 5*11^3 + 4*11^4 + O(11^5)
            sage: R(1/32)
            10 + 7*11 + 11^2 + 5*11^3 + 4*11^4 + O(11^5)
            sage: R(1/2)^5 == R(1/32)
            True
            sage: R(3)^1000
            1 + 4*11^2 + 3*11^3 + 7*11^4 + O(11^5)
        """
        cdef long base_level, exp_prec, relprec, val
        cdef mpz_t tmp
        cdef Integer right
        cdef CAElement u, base, ans = self._new_c()
        if isinstance(_right, (int, long, Integer)) and _right == 0:
            # return 1 to maximum precision
            ans.absprec = self.prime_pow.prec_cap
            csetone(ans.value, ans.prime_pow)
        elif ciszero(self.value, self.prime_pow):
            # If a positive integer exponent, return an inexact zero of valuation right * self.ordp.  Otherwise raise an error.
            if isinstance(_right, (int, long)):
                _right = Integer(_right)
            if PY_TYPE_CHECK(_right, Integer):
                if _right < 0:
                    raise ValueError, "Need more precision"
                if self.absprec == self.prime_pow.prec_cap or mpz_cmp_si((<Integer>_right).value, self.prime_pow.prec_cap / self.absprec + 1) > 0:
                    ans.absprec = self.prime_pow.prec_cap
                else:
                    ans.absprec = min(self.prime_pow.prec_cap, self.absprec * mpz_get_si((<Integer>_right).value))
                csetzero(ans.value, ans.prime_pow)
            elif PY_TYPE_CHECK(_right, Rational) or (PY_TYPE_CHECK(_right, pAdicGenericElement) and _right._is_base_elt(self.prime_pow.prime)):
                raise ValueError("Need more precision")
            else:
                raise TypeError, "exponent must be an integer, rational or base p-adic with the same prime"
        else:
            val = self.valuation_c()
            # pow_helper is defined in padic_template_element.pxi
            right = pow_helper(&relprec, &exp_prec, val, self.absprec - val, _right, self.prime_pow)
            if exp_prec == 0:
                # a p-adic exponent with no relative precision
                ans.absprec = 0
                csetzero(ans.value, ans.prime_pow)
                return ans
            elif exp_prec > 0 and exp_prec < relprec - 1:
                # p-adic exponent that potentially imposes a lower precision
                u = self.unit_part()
                # Exponentiation by a p-adic exponent only makes sense if the
                # base reduces to an element of F_p modulo the uniformizer.

                # We want to compute the "level," namely the valuation
                # k of `u/T - 1`, where T is the Teichmuller
                # representative of u.  I claim that k is the
                # valuation of u - u^p.  Let M be a unit such that
                # u/T = 1 + pi^k*M.  Then
                # u^p/T = (1 + pi^k*M)^p = 1 (mod pi^(k+1)).
                # Thus u - u^p = T*M*p^k (mod p^(k+1))

                # We use ans.value as a temporary variable.
                cpow(ans.value, u.value, self.prime_pow.prime.value, u.absprec, self.prime_pow)
                csub(ans.value, ans.value, u.value, u.absprec, self.prime_pow)
                relprec = padic_exp_helper(relprec, exp_prec, cvaluation(ans.value, u.absprec, self.prime_pow), self.prime_pow)
            mpz_init_set_si(tmp, val)
            mpz_mul(tmp, right.value, tmp)
            if mpz_cmp_si(tmp, self.prime_pow.prec_cap) >= 0:
                ans.absprec = self.prime_pow.prec_cap
                csetzero(ans.value, ans.prime_pow)
            else:
                ans.absprec = min(mpz_get_si(tmp) + relprec, self.prime_pow.prec_cap)
                if right < 0:
                    base = ~self
                    right = -right
                else:
                    base = self
                cpow(ans.value, base.value, right.value, ans.absprec, ans.prime_pow)
            mpz_clear(tmp)
        return ans
        
    cdef pAdicTemplateElement _lshift_c(self, long shift):
        """
        Multiplies by ``p^shift``.

        TESTS::

            sage: R = ZpCA(5); a = R(17); a << 2
            2*5^2 + 3*5^3 + O(5^20)
        """
        if shift < 0:
            return self._rshift_c(-shift)
        elif shift == 0:
            return self
        cdef CAElement ans = self._new_c()
        if shift >= self.prime_pow.prec_cap:
            csetzero(ans.value, ans.prime_pow)
            ans.absprec = self.prime_pow.prec_cap
        else:
            ans.absprec = min(self.absprec + shift, self.prime_pow.prec_cap)
            cshift(ans.value, self.value, shift, ans.absprec, ans.prime_pow, False)
        return ans

    cdef pAdicTemplateElement _rshift_c(self, long shift):
        """
        Divides by ``p^shift`` and truncates.

        TESTS::

            sage: R = ZpCA(5); a = R(77); a >> 1
            3*5 + O(5^19)
        """
        if shift < 0:
            return self._lshift_c(-shift)
        elif shift == 0:
            return self
        cdef CAElement ans = self._new_c()
        if shift >= self.absprec:
            csetzero(ans.value, ans.prime_pow)
            ans.absprec = 0
        else:
            ans.absprec = self.absprec - shift
            cshift(ans.value, self.value, -shift, ans.absprec, ans.prime_pow, False)
        return ans

    def add_bigoh(self, absprec):
        """
        Returns a new element with absolute precision decreased to
        ``prec``.  The precision never increases.
        
        INPUT:
        
        - ``self`` -- a `p`-adic element
        
        - ``prec`` -- an integer
            
        OUTPUT:
        
        - ``element`` -- ``self`` with precision set to the minimum of ``self's`` precision and ``prec``
        
        EXAMPLES::
        
            sage: R = Zp(7,4,'capped-abs','series'); a = R(8); a.add_bigoh(1)
            1 + O(7)

            sage: k = ZpCA(3,5)
            sage: a = k(41); a
            2 + 3 + 3^2 + 3^3 + O(3^5)
            sage: a.add_bigoh(7)
            2 + 3 + 3^2 + 3^3 + O(3^5)
            sage: a.add_bigoh(3)
            2 + 3 + 3^2 + O(3^3)            
        """
        cdef long aprec, newprec
        if PY_TYPE_CHECK(absprec, int):
            aprec = absprec
        else:
            if not PY_TYPE_CHECK(absprec, Integer):
                absprec = Integer(absprec)
            aprec = mpz_get_si((<Integer>absprec).value)
        if aprec >= self.absprec:
            return self
        cdef CAElement ans = self._new_c()
        ans.absprec = aprec
        creduce(ans.value, self.value, ans.absprec, ans.prime_pow)
        return ans

    cpdef bint _is_exact_zero(self) except -1:
        return False

    cpdef bint _is_inexact_zero(self) except -1:
        """
        Returns ``True`` if ``self`` is indistinguishable from zero.
        
        EXAMPLES::
        
            sage: R = ZpCA(7, 5)
            sage: R(7^5)._is_inexact_zero()
            True
            sage: R(0,4)._is_inexact_zero()
            True
            sage: R(0)._is_inexact_zero()
            True
        """
        return ciszero(self.value, self.prime_pow)

    def is_zero(self, absprec = None):
        r"""
        Returns whether ``self`` is zero modulo ``p^absprec``.
        
        INPUT:
        
        - ``self`` -- a `p`-adic element
        
        - ``prec`` -- an integer

        OUTPUT:
        
        - ``boolean`` -- whether self is zero
          
        EXAMPLES::
        
            sage: R = ZpCA(17, 6)
            sage: R(0).is_zero()
            True
            sage: R(17^6).is_zero()
            True
            sage: R(17^2).is_zero(absprec=2)
            True
        """
        cdef bint iszero = ciszero(self.value, self.prime_pow)
        if absprec is None:
            return iszero
        cdef long val = self.valuation_c()
        if isinstance(absprec, int):
            if iszero and absprec > self.absprec:
                raise PrecisionError, "Not enough precision to determine if element is zero"
            return val >= absprec
        if not PY_TYPE_CHECK(absprec, Integer):
            absprec = Integer(absprec)
        if iszero:
            if mpz_cmp_si((<Integer>absprec).value, val) > 0:
                raise PrecisionError, "Not enough precision to determine if element is zero"
            else:
                return True
        return mpz_cmp_si((<Integer>absprec).value, val) <= 0

    def __nonzero__(self):
        return not ciszero(self.value, self.prime_pow)

    def is_equal_to(self, _right, absprec=None):
        r"""
        Returns whether ``self`` is equal to ``right`` modulo ``p^absprec``.

        INPUT:
        
        - ``self`` -- a `p`-adic element
        
        - ``right`` -- a `p`-adic element with the same parent
        
        - ``absprec`` -- an integer

        OUTPUT:
        
        - ``boolean`` -- whether ``self`` is equal to ``right``
          
        EXAMPLES::
        
            sage: R = ZpCA(2, 6)
            sage: R(13).is_equal_to(R(13))
            True
            sage: R(13).is_equal_to(R(13+2^10))
            True
            sage: R(13).is_equal_to(R(17), 2)
            True
            sage: R(13).is_equal_to(R(17), 5)
            False
        """
        cdef CAElement right
        cdef long aprec, rprec, sval, rval
        if self.parent() is _right.parent():
            right = <CAElement>_right
        else:
            right = <CAElement>self.parent()(_right)
        if absprec is None:
            aprec = min(self.absprec, right.absprec)
        else:
            if not PY_TYPE_CHECK(absprec, Integer):
                absprec = Integer(absprec)
            if mpz_fits_slong_p((<Integer>absprec).value) == 0:
                if mpz_sgn((<Integer>absprec).value) < 0:
                    return True
                else:
                    raise PrecisionError, "Elements not known to enough precision"
            aprec = mpz_get_si((<Integer>absprec).value)
            if aprec > self.absprec or aprec > right.absprec:
                raise PrecisionError, "Elements not known to enough precision"
        return ccmp(self.value, right.value, aprec, aprec < self.absprec, aprec < right.absprec, self.prime_pow) == 0

    cdef int _cmp_units(self, pAdicGenericElement _right):
        cdef CAElement right = <CAElement>_right
        cdef long aprec = min(self.absprec, right.absprec)
        if aprec == 0:
            return 0
        return ccmp(self.value, right.value, aprec, aprec < self.absprec, aprec < right.absprec, self.prime_pow)

    cdef pAdicTemplateElement lift_to_precision_c(self, long absprec):
        if absprec <= self.absprec:
            return self
        cdef CAElement ans = self._new_c()
        ccopy(ans.value, self.value, ans.prime_pow)
        ans.absprec = absprec
        return ans

    def list(self, lift_mode = 'simple'):
        """
        Returns a list of coefficients of `p` starting with `p^0`
        
        INPUT:
        
        - ``self`` -- a `p`-adic element
        
        - ``lift_mode`` -- ``'simple'``, ``'smallest'`` or
          ``'teichmuller'`` (default ``'simple'``)

        OUTPUT:
        
        - ``list`` -- the list of coefficients of ``self``

        NOTES:
        
        - Returns a list `[a_0, a_1, \ldots, a_n]` so that:

          + If ``lift_mode = 'simple'``, `a_i` is an integer with `0
            \le a_i < p`.

          + If ``lift_mode = 'smallest'``, `a_i` is an integer with
            `-p/2 < a_i \le p/2`.

          + If ``lift_mode = 'teichmuller'``, `a_i` has the same
            parent as `self` and `a_i^p \equiv a_i` modulo
            ``p^(self.precision_absolute() - i)``

        - `\sum_{i = 0}^n a_i \cdot p^i =` ``self``, modulo the
          precision of ``self``.
            

        EXAMPLES::
        
            sage: R = ZpCA(7,6); a = R(12837162817); a
            3 + 4*7 + 4*7^2 + 4*7^4 + O(7^6)
            sage: L = a.list(); L
            [3, 4, 4, 0, 4]
            sage: sum([L[i] * 7^i for i in range(len(L))]) == a
            True
            sage: L = a.list('smallest'); L
            [3, -3, -2, 1, -3, 1]
            sage: sum([L[i] * 7^i for i in range(len(L))]) == a
            True
            sage: L = a.list('teichmuller'); L
            [3 + 4*7 + 6*7^2 + 3*7^3 + 2*7^5 + O(7^6),
            O(7^5),
            5 + 2*7 + 3*7^3 + O(7^4),
            1 + O(7^3),
            3 + 4*7 + O(7^2),
            5 + O(7)]
            sage: sum([L[i] * 7^i for i in range(len(L))])
            3 + 4*7 + 4*7^2 + 4*7^4 + O(7^6)
        """
        if ciszero(self.value, self.prime_pow):
            return []
        if lift_mode == 'teichmuller':
            return self.teichmuller_list()
        elif lift_mode == 'simple':
            return clist(self.value, self.absprec, True, self.prime_pow)
        elif lift_mode == 'smallest':
            return clist(self.value, self.absprec, False, self.prime_pow)
        else:
            raise ValueError, "unknown lift_mode"

    def teichmuller_list(self):
        r"""
        Returns a list `[a_0, a_1,\ldots, a_n]` such that

        - `a_i^p = a_i`

        - ``self`` equals `\sum_{i = 0}^n a_i p^i`

        - if `a_i \ne 0`, the absolute precision of `a_i` is
          ``self.precision_relative() - i``

        EXAMPLES::

            sage: R = ZpCA(5,5); R(14).list('teichmuller') #indirect doctest
            [4 + 4*5 + 4*5^2 + 4*5^3 + 4*5^4 + O(5^5),
            3 + 3*5 + 2*5^2 + 3*5^3 + O(5^4),
            2 + 5 + 2*5^2 + O(5^3),
            1 + O(5^2),
            4 + O(5)]
        """
        ans = PyList_New(0)
        if ciszero(self.value, self.prime_pow):
            return ans
        cdef long curpower = self.absprec
        cdef CAElement list_elt
        cdef CAElement tmp = self._new_c()
        ccopy(tmp.value, self.value, self.prime_pow)
        while not ciszero(tmp.value, tmp.prime_pow) and curpower > 0:
            list_elt = self._new_c()
            cteichmuller(list_elt.value, tmp.value, curpower, self.prime_pow)
            if ciszero(list_elt.value, self.prime_pow):
                cshift0(tmp.value, tmp.value, -1, curpower-1, self.prime_pow)
            else:
                csub(tmp.value, tmp.value, list_elt.value, curpower, self.prime_pow)
                cshift0(tmp.value, tmp.value, -1, curpower-1, self.prime_pow)
                creduce(tmp.value, tmp.value, curpower-1, self.prime_pow)
            list_elt.absprec = curpower
            curpower -= 1
            PyList_Append(ans, list_elt)
        return ans

    def _teichmuller_set(self):
        """
        Sets ``self`` to be the Teichmuller representative with the
        same residue as ``self``.

        WARNING:

        This function modifies ``self``, which is not safe.  Elements
        are supposed to be immutable.

        EXAMPLES::

            sage: R = ZpCA(17,5); a = R(11)
            sage: a
            11 + O(17^5)
            sage: a._teichmuller_set(); a
            11 + 14*17 + 2*17^2 + 12*17^3 + 15*17^4 + O(17^5)
            sage: a.list('teichmuller')
            [11 + 14*17 + 2*17^2 + 12*17^3 + 15*17^4 + O(17^5)]
        """
        if self.valuation_c() > 0:
            csetzero(self.value, self.prime_pow)
            self.absprec = self.prime_pow.prec_cap
        elif self.absprec == 0:
            raise ValueError("not enough precision")
        else:
            cteichmuller(self.value, self.value, self.absprec, self.prime_pow)

    def precision_absolute(self):
        """
        Returns the absolute precision of ``self``.

        This is the power of the maximal ideal modulo which this
        element is defined.
        
        INPUT:
        
        - ``self`` -- a `p`-adic element
            
        OUTPUT:
        
        - ``integer`` -- the absolute precision of ``self``
            
        EXAMPLES::
        
            sage: R = Zp(7,4,'capped-abs'); a = R(7); a.precision_absolute()
            4
       """
        cdef Integer ans = PY_NEW(Integer)
        mpz_set_si(ans.value, self.absprec)
        return ans

    def precision_relative(self):
        """
        Returns the relative precision of ``self``.

        This is the power of the maximal ideal modulo which the unit
        part of ``self`` is defined.
        
        INPUT:
        
        - ``self`` -- a `p`-adic element
            
        OUTPUT:
        
        - ``integer`` -- the relative precision of ``self``

        EXAMPLES::
        
            sage: R = Zp(7,4,'capped-abs'); a = R(7); a.precision_relative()
            3
       """
        cdef Integer ans = PY_NEW(Integer)
        mpz_set_si(ans.value, self.absprec - self.valuation_c())
        return ans

    cpdef pAdicTemplateElement unit_part(CAElement self):
        r"""
        Returns the unit part of ``self``.

        INPUT:
        
        - ``self`` -- a `p`-adic element
            
        OUTPUT:
        
        - `p`-adic element -- the unit part of ``self``
            
        EXAMPLES::
        
            sage: R = Zp(17,4,'capped-abs', 'val-unit')
            sage: a = R(18*17)
            sage: a.unit_part()
            18 + O(17^3)
            sage: type(a)
            <type 'sage.rings.padics.padic_capped_absolute_element.pAdicCappedAbsoluteElement'>
        """
        cdef CAElement ans = (<CAElement>self)._new_c()
        cdef long val = cremove(ans.value, (<CAElement>self).value, (<CAElement>self).absprec, (<CAElement>self).prime_pow)
        ans.absprec = (<CAElement>self).absprec - val
        return ans

    cdef long valuation_c(self):
        """
        Returns the valuation of this element.

        TESTS::
        
            sage: R = ZpCA(5)
            sage: R(5^5*1827).valuation()
            5
            sage: R(1).valuation()
            0
            sage: R(2).valuation()
            0
            sage: R(5).valuation()
            1
            sage: R(10).valuation()
            1
            sage: R(25).valuation()
            2
            sage: R(50).valuation()
            2            
            sage: R(0).valuation()
            20
            sage: R(0,6).valuation()
            6
        """
        # for backward compatibility
        return cvaluation(self.value, self.absprec, self.prime_pow)

    cpdef val_unit(self):
        """
        Returns a 2-tuple, the first element set to the valuation of
        ``self``, and the second to the unit part of ``self``.

        If ``self = 0``, then the unit part is ``O(p^0)``.

        EXAMPLES::
        
            sage: R = ZpCA(5)
            sage: a = R(75, 6); b = a - a
            sage: a.val_unit()
            (2, 3 + O(5^4))
            sage: b.val_unit()
            (6, O(5^0))
        """
        cdef CAElement unit = self._new_c()
        cdef Integer valuation = PY_NEW(Integer)
        cdef long val = cremove(unit.value, self.value, self.absprec, self.prime_pow)
        mpz_set_si(valuation.value, val)
        unit.absprec = self.absprec - val
        return valuation, unit

    def __hash__(self):
        """
        Hashing.
        
        EXAMPLES::
        
            sage: R = ZpCA(11, 5)
            sage: hash(R(3)) == hash(3)
            True
        """
        return chash(self.value, 0, self.absprec, self.prime_pow)

cdef class pAdicCoercion_ZZ_CA(RingHomomorphism_coercion):
    """
    The canonical inclusion from ZZ to a capped absolute ring.

    EXAMPLES::

        sage: f = ZpCA(5).coerce_map_from(ZZ); f
        Ring Coercion morphism:
          From: Integer Ring
          To:   5-adic Ring with capped absolute precision 20
    """
    def __init__(self, R):
        """
        Initialization.

        EXAMPLES::

            sage: f = ZpCA(5).coerce_map_from(ZZ); type(f)
            <type 'sage.rings.padics.padic_capped_absolute_element.pAdicCoercion_ZZ_CA'>
        """
        RingHomomorphism_coercion.__init__(self, ZZ.Hom(R), check=False)
        self._zero = R._element_constructor(R, 0)
        self._section = pAdicConvert_CA_ZZ(R)

    cpdef Element _call_(self, x):
        """
        Evaluation.

        EXAMPLES::

            sage: f = ZpCA(5).coerce_map_from(ZZ)
            sage: f(0).parent()
            5-adic Ring with capped absolute precision 20
            sage: f(5)
            5 + O(5^20)
        """
        if mpz_sgn((<Integer>x).value) == 0:
            return self._zero
        cdef CAElement ans = self._zero._new_c()
        ans.absprec = ans.prime_pow.prec_cap
        cconv_mpzt(ans.value, (<Integer>x).value, ans.absprec, True, ans.prime_pow)
        return ans

    cpdef Element _call_with_args(self, x, args=(), kwds={}):
        """
        This function is used when some precision cap is passed in (relative or absolute or both).

        See the documentation for pAdicCappedAbsoluteElement.__init__ for more details.

        EXAMPLES::

            sage: R = ZpCA(5,4)
            sage: type(R(10,2))
            <type 'sage.rings.padics.padic_capped_absolute_element.pAdicCappedAbsoluteElement'>
            sage: R(10,2)
            2*5 + O(5^2)
            sage: R(10,3,1)
            2*5 + O(5^2)
            sage: R(10,absprec=2)
            2*5 + O(5^2)
            sage: R(10,relprec=2)
            2*5 + O(5^3)
            sage: R(10,absprec=1)
            O(5)
            sage: R(10,empty=True)
            O(5^0)
        """
        cdef long val, aprec, rprec
        cdef CAElement ans
        _process_args_and_kwds(&aprec, &rprec, args, kwds, True, self._zero.prime_pow)
        if mpz_sgn((<Integer>x).value) == 0:
            if aprec >= self._zero.prime_pow.prec_cap:
                return self._zero
            ans = self._zero._new_c()
            csetzero(ans.value, ans.prime_pow)
            ans.absprec = aprec
        else:
            val = get_ordp(x, self._zero.prime_pow)
            ans = self._zero._new_c()
            if aprec <= val:
                csetzero(ans.value, ans.prime_pow)
                ans.absprec = aprec
            else:
                ans.absprec = min(aprec, val + rprec)
                cconv_mpzt(ans.value, (<Integer>x).value, ans.absprec, True, self._zero.prime_pow)
        return ans

    def section(self):
        """
        Returns a map back to ZZ that approximates an element of Zp by an integer.

        EXAMPLES::

            sage: f = ZpCA(5).coerce_map_from(ZZ).section()
            sage: f(ZpCA(5)(-1)) - 5^20
            -1
        """
        return self._section

cdef class pAdicConvert_CA_ZZ(RingMap):
    """
    The map from a capped absolute ring back to ZZ that returns the the smallest non-negative integer
    approximation to its input which is accurate up to the precision.

    If the input is not in the closure of the image of ZZ, raises a ValueError.

    EXAMPLES::

        sage: f = ZpCA(5).coerce_map_from(ZZ).section(); f
        Set-theoretic ring morphism:
          From: 5-adic Ring with capped absolute precision 20
          To:   Integer Ring
    """
    def __init__(self, R):
        """
        Initialization.

        EXAMPLES::

            sage: f = ZpCA(5).coerce_map_from(ZZ).section(); type(f)
            <type 'sage.rings.padics.padic_capped_absolute_element.pAdicConvert_CA_ZZ'>
            sage: f.category()
            Category of hom sets in Category of sets
        """
        if R.degree() > 1 or R.characteristic() != 0 or R.residue_characteristic() == 0:
            RingMap.__init__(self, Hom(R, ZZ, SetsWithPartialMaps()))
        else:
            RingMap.__init__(self, Hom(R, ZZ, Sets()))

    cpdef Element _call_(self, _x):
        """
        Evaluation.

        EXAMPLES::

            sage: f = ZpCA(5).coerce_map_from(ZZ).section()
            sage: f(ZpCA(5)(-1)) - 5^20
            -1
            sage: f(ZpCA(5)(0))
            0
        """
        cdef Integer ans = PY_NEW(Integer)
        cdef CAElement x = <CAElement>_x
        cconv_mpzt_out(ans.value, x.value, 0, x.absprec, x.prime_pow)
        return ans

cdef class pAdicConvert_QQ_CA(Morphism):
    """
    The inclusion map from QQ to a capped absolute ring that is defined
    on all elements with non-negative p-adic valuation.

    EXAMPLES::
    
        sage: f = ZpCA(5).convert_map_from(QQ); f
        Generic morphism:
          From: Rational Field
          To:   5-adic Ring with capped absolute precision 20
    """
    def __init__(self, R):
        """
        Initialization.

        EXAMPLES::

            sage: f = ZpCA(5).convert_map_from(QQ); type(f)
            <type 'sage.rings.padics.padic_capped_absolute_element.pAdicConvert_QQ_CA'>
        """
        Morphism.__init__(self, Hom(QQ, R, SetsWithPartialMaps()))
        self._zero = R._element_constructor(R, 0)

    cpdef Element _call_(self, x):
        """
        Evaluation.

        EXAMPLES::

            sage: f = ZpCA(5,4).convert_map_from(QQ)
            sage: f(1/7)
            3 + 3*5 + 2*5^3 + O(5^4)
            sage: f(0)
            O(5^4)
        """
        if mpq_sgn((<Rational>x).value) == 0:
            return self._zero
        cdef CAElement ans = self._zero._new_c()
        cconv_mpqt(ans.value, (<Rational>x).value, ans.prime_pow.prec_cap, True, ans.prime_pow)
        ans.absprec = ans.prime_pow.prec_cap
        return ans

    cpdef Element _call_with_args(self, x, args=(), kwds={}):
        """
        This function is used when some precision cap is passed in (relative or absolute or both).

        See the documentation for pAdicCappedAbsoluteElement.__init__ for more details.

        EXAMPLES::

            sage: R = ZpCA(5,4)
            sage: type(R(10/3,2))
            <type 'sage.rings.padics.padic_capped_absolute_element.pAdicCappedAbsoluteElement'>
            sage: R(10/3,2)
            4*5 + O(5^2)
            sage: R(10/3,3,1)
            4*5 + O(5^2)
            sage: R(10/3,absprec=2)
            4*5 + O(5^2)
            sage: R(10/3,relprec=2)
            4*5 + 5^2 + O(5^3)
            sage: R(10/3,absprec=1)
            O(5)
            sage: R(10/3,empty=True)
            O(5^0)
            sage: R(3/100,relprec=3)
            Traceback (most recent call last):
            ...
            ValueError: p divides denominator
        """
        cdef long val, aprec, rprec
        cdef CAElement ans
        _process_args_and_kwds(&aprec, &rprec, args, kwds, True, self._zero.prime_pow)
        if mpq_sgn((<Rational>x).value) == 0:
            if aprec >= self._zero.prime_pow.prec_cap:
                return self._zero
            ans = self._zero._new_c()
            csetzero(ans.value, ans.prime_pow)
            ans.absprec = aprec
        else:
            val = get_ordp(x, self._zero.prime_pow)
            ans = self._zero._new_c()
            if aprec <= val:
                csetzero(ans.value, ans.prime_pow)
                ans.absprec = aprec
            else:
                ans.absprec = min(aprec, val + rprec)
                cconv_mpqt(ans.value, (<Rational>x).value, ans.absprec, True, self._zero.prime_pow)
        return ans

def unpickle_cae_v2(cls, parent, value, absprec):
    cdef CAElement ans = PY_NEW(cls)
    ans._parent = parent
    ans.prime_pow = <PowComputer_class?>parent.prime_pow
    cconstruct(ans.value, ans.prime_pow)
    cunpickle(ans.value, value, ans.prime_pow)
    ans.absprec = absprec
    return ans
