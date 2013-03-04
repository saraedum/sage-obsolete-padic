"""
Tests for `p`-adic rings and their elements

This file tests several aspects of `p`-adic rings and their elements which can
not be conveniently tested in doctests. Mostly these are tests on arithmetic
for random elements and tests for cython methods which can not be called
directly in a docstring.

AUTHORS:

- Julian Rueth (2013-02-27): initial version
"""

class Arithmetic(object):
    """
    Generic tests for `p`-adic arithmetic.

    INPUT:

    - ``elements`` -- a list of (random) elements used to perform the tests

    EXAMPLES::

        sage: from sage.rings.padics.test import Arithmetic
        sage: R = Zp(3)
        sage: Arithmetic(R, R.some_elements())
        <sage.rings.padics.test.Arithmetic object at ...>

    """
    def __init__(self, parent, elements):
        """
        Initialize an object which bundles arithmetic tests.

        TESTS::

            sage: from sage.rings.padics.test import Arithmetic
            sage: R = Zp(3)
            sage: type(Arithmetic(R, R.some_elements()))
            <class 'sage.rings.padics.test.Arithmetic'>

        """
        self._parent = parent
        self._elements = elements

    def run(self):
        """
        Run all tests.

        EXAMPLES::

            sage: from sage.rings.padics.test import Arithmetic
            sage: R = Zp(3)
            sage: Arithmetic(R, R.some_elements()).run()

        """
        self._test_neg()
        self._test_add()
        self._test_sub()
        self._test_invert()
        self._test_mul()

    def _test_neg(self):
        """
        Test the negation operator.

        EXAMPLES::

            sage: from sage.rings.padics.test import Arithmetic
            sage: R = Zp(3)
            sage: Arithmetic(R, R.some_elements())._test_neg()

        """
        for x in self._elements:
            y = -x
            assert y.parent() is self._parent
            assert (x+y).is_zero()
            assert y.valuation() == x.valuation()
            assert x.precision_absolute() == y.precision_absolute()
            assert x.precision_relative() == y.precision_relative()
            assert x.is_zero() == y.is_zero()
            assert x.is_unit() == y.is_unit()

    def _test_add(self):
        """
        Test addition.

        EXAMPLES::

            sage: from sage.rings.padics.test import Arithmetic
            sage: R = Zp(3)
            sage: Arithmetic(R, R.some_elements())._test_add()

        """
        for x in self._elements:
            y = x + self._parent.zero()
            assert y == x
            assert y.precision_absolute() == x.precision_absolute()
            assert y.precision_relative() == x.precision_relative()

        from random import sample
        for i in range(len(self._elements)):
            x,y  = sample(self._elements, 2)
            z = x + y
            assert z.parent() is self._parent
            assert z.precision_absolute() <= min(x.precision_absolute(), y.precision_absolute())
            assert z.valuation() >= min(x.valuation(),y.valuation())
            if x.valuation() != y.valuation(): assert z.valuation() == min(x.valuation(),y.valuation())
            assert z - x == y
            assert z - y == x

    def _test_sub(self):
        """
        Test subtraction.

        EXAMPLES::

            sage: from sage.rings.padics.test import Arithmetic
            sage: R = Zp(3)
            sage: Arithmetic(R, R.some_elements())._test_sub()

        """
        for x in self._elements:
            y = x - self._parent.zero()
            assert y == x
            assert y.precision_absolute() == x.precision_absolute()
            assert y.precision_relative() == x.precision_relative()

        from random import sample
        for i in range(len(self._elements)):
            x,y  = sample(self._elements, 2)
            z = x - y
            assert z.parent() is self._parent
            assert z.precision_absolute() <= min(x.precision_absolute(), y.precision_absolute())
            assert z.valuation() >= min(x.valuation(),y.valuation())
            if x.valuation() != y.valuation(): assert z.valuation() == min(x.valuation(),y.valuation())
            assert z - x == -y
            assert z + y == x

    def _test_invert(self):
        """
        Test multiplicative inversion.

        EXAMPLES::

            sage: from sage.rings.padics.test import Arithmetic
            sage: R = Zp(3)
            sage: Arithmetic(R, R.some_elements())._test_sub()

        """
        for x in self._elements:
            if x.is_unit():
                y = ~x
                e = y * x
                assert y.parent() is self._parent.fraction_field()
                assert e.is_one()
                assert e.precision_relative() >= x.precision_relative()
                assert y.valuation() == -x.valuation()
            else:
                try:
                    y = ~x
                except ZeroDivisionError, TypeError: pass
                else:
                    assert not y.parent() is x.parent() and y.parent() is x.parent().fraction_field()

    def _test_mul(self):
        """
        Test multiplication.

        EXAMPLES::

            sage: from sage.rings.padics.test import Arithmetic
            sage: R = Zp(3)
            sage: Arithmetic(R, R.some_elements())._test_mul()

        """
        from random import sample
        for i in range(len(self._elements)):
            x,y  = sample(self._elements, 2)
            z = x * y
            assert z.parent() is self._parent
            assert z.precision_relative() <= min(x.precision_relative(), y.precision_relative())
            assert z.valuation() == x.valuation() + y.valuation() or z.is_zero()
