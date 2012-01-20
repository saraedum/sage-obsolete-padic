"""
Accurate timing information for Sage commands

This is an implementation of nice timeit functionality, like the
``%timeit`` magic command in IPython.  To use it, use the ``timeit``
command. This command then calls :func:`sage_timeit`, which you can
find below.

EXAMPLES::

    sage: timeit('1+1')    # random output
    625 loops, best of 3: 314 ns per loop

AUTHOR:

    -- William Stein, based on code by Fernando Perez included in IPython
"""


class SageTimeitResult():
    r""" 
    Represent the statistics of a timeit() command.  

    Prints as a string so that it can be easily returned to a user.

    INPUT:

    - ``stats`` -- tuple of length 5 containing the following information:
        
        - integer, number of loops
        - integer, repeat number
        - Python integer, number of digits to print
        - number, best timing result
        - str, time unit

    EXAMPLES::

        sage: from sage.misc.sage_timeit import SageTimeitResult
        sage: SageTimeitResult( (3, 5, int(8), pi, 'ms') )
        3 loops, best of 5: 3.1415927 ms per loop

    ::
        
        sage: units = ["s", "ms", "\xc2\xb5s", "ns"]
        sage: scaling = [1, 1e3, 1e6, 1e9]
        sage: number = 7   
        sage: repeat = 13
        sage: precision = int(5)
        sage: best = pi / 10 ^ 9
        sage: order = 3
        sage: stats = (number, repeat, precision, best * scaling[order], units[order])    
        sage: SageTimeitResult(stats)
        7 loops, best of 13: 3.1416 ns per loop

    If the third argument is not a Python integer, a ``TypeError`` is raised::

        sage: SageTimeitResult( (1, 2, 3, 4, 's') )
        Traceback (most recent call last):
        ...
        TypeError: * wants int

    """
    def __init__(self, stats):
        r"""
        Construction of a timing result.

        See documentation of ``SageTimeitResult`` for more details and
        examples.

        EXAMPLES::

            sage: from sage.misc.sage_timeit import SageTimeitResult
            sage: SageTimeitResult( (3, 5, int(8), pi, 'ms') )
            3 loops, best of 5: 3.1415927 ms per loop
        """
        self.stats = stats

    def __repr__(self):
        r"""
        String representation.

        EXAMPLES::

            sage: from sage.misc.sage_timeit import SageTimeitResult
            sage: stats = (1, 2, int(3), pi, 'ns')
            sage: SageTimeitResult(stats)           #indirect doctest
            1 loops, best of 2: 3.14 ns per loop
        """
        return "%d loops, best of %d: %.*g %s per loop" % self.stats

def sage_timeit(stmt, globals_dict=None, preparse=None, number=0, repeat=3, precision=3, seconds=False):
    """
    Accurately measure the wall time required to execute ``stmt``.

    INPUT:

    - ``stmt`` -- a text string.

    - ``globals_dict`` -- a dictionary or ``None`` (default). Evaluate
      ``stmt`` in the context of the globals dictionary. If not set,
      the current ``globals()`` dictionary is used.

    - ``preparse`` -- (default: use globals preparser default) if
      ``True`` preparse ``stmt`` using the Sage preparser.

    - ``number`` -- integer, (optional, default: 0), number of loops.

    - ``repeat`` -- integer, (optional, default: 3), number of
      repetition.

    - ``precision`` -- integer, (optional, default: 3), precision of
      output time.

    - ``seconds`` -- boolean (default: ``False``). Whether to just
      return time in seconds.

    OUTPUT:

    An instance of ``SageTimeitResult`` unless the optional parameter
    ``seconds=True`` is passed. In that case, the elapsed time in
    seconds is returned as a floating-point number.

    EXAMPLES::

        sage: from sage.misc.sage_timeit import sage_timeit
        sage: sage_timeit('3^100000', globals(), preparse=True, number=50)      # random output
        '50 loops, best of 3: 1.97 ms per loop'
        sage: sage_timeit('3^100000', globals(), preparse=False, number=50)     # random output
        '50 loops, best of 3: 67.1 ns per loop'
        sage: a = 10
        sage: sage_timeit('a^2', globals(), number=50)                            # random output
        '50 loops, best of 3: 4.26 us per loop'

    It's usually better to use the ``timeit`` object, usually::

        sage: timeit('10^2', number=50)
        50 loops, best of 3: ... per loop

    The input expression can contain newlines (but doctests cannot, so
    we use ``os.linesep`` here)::

        sage: from sage.misc.sage_timeit import sage_timeit
        sage: from os import linesep as CR
        sage: # sage_timeit(r'a = 2\\nb=131\\nfactor(a^b-1)')
        sage: sage_timeit('a = 2' + CR + 'b=131' + CR + 'factor(a^b-1)', 
        ...               globals(), number=10)
        10 loops, best of 3: ... per loop

    Test to make sure that ``timeit`` behaves well with output::

        sage: timeit("print 'Hi'", number=50)
        50 loops, best of 3: ... per loop

    If you want a machine-readable output, use the ``seconds=True`` option::

        sage: timeit("print 'Hi'", seconds=True)   # random output
        1.42555236816e-06
        sage: t = timeit("print 'Hi'", seconds=True)
        sage: t     #r random output
        3.6010742187499999e-07

    TESTS:

    Make sure that garbage collection is re-enabled after an exception
    occurs in timeit::

        sage: def f(): raise ValueError
        sage: import gc
        sage: gc.isenabled()
        True
        sage: timeit("f()")
        Traceback (most recent call last):
        ...
        ValueError
        sage: gc.isenabled()
        True
    """
    import timeit as timeit_, time, math, preparser, interpreter
    number=int(number)
    repeat=int(repeat)
    precision=int(precision)
    if preparse is None:
        preparse = interpreter.do_preparse
    if preparse:
        stmt = preparser.preparse(stmt)
    if stmt == "":
        return ''

    units = ["s", "ms", "\xc2\xb5s", "ns"]
    scaling = [1, 1e3, 1e6, 1e9]

    timer = timeit_.Timer()

    # this code has tight coupling to the inner workings of timeit.Timer,
    # but is there a better way to achieve that the code stmt has access
    # to the shell namespace?

    src = timeit_.template % {'stmt': timeit_.reindent(stmt, 8),
                             'setup': "pass"}
    code = compile(src, "<magic-timeit>", "exec")
    ns = {}
    if not globals_dict:
        globals_dict = globals()
    exec code in globals_dict, ns
    timer.inner = ns["inner"]


    try:
        import sys
        f = sys.stdout
        sys.stdout = open('/dev/null', 'w')

        if number == 0:
            # determine number so that 0.2 <= total time < 2.0
            number = 1
            for i in range(1, 5):
                number *= 5
                if timer.timeit(number) >= 0.2:
                    break

        best = min(timer.repeat(repeat, number)) / number

    finally:
        sys.stdout.close()
        sys.stdout = f
        import gc
        gc.enable()

    if seconds:
        return best

    if best > 0.0:
        order = min(-int(math.floor(math.log10(best)) // 3), 3)
    else:
        order = 3
    stats = (number, repeat, precision, best * scaling[order], units[order])
    return SageTimeitResult(stats)
