"""
Interpolation algorithms for Guruswami-Sudan decoder

AUTHORS:

- Johan S. R. Nielsen, original implementation (see [Nielsen]_ for details)
- David Lucas, ported the original implementation in Sage
"""

#*****************************************************************************
#       Copyright (C) 2015 David Lucas <david.lucas@inria.fr>
#                     2015 Johan S. R. Nielsen <jsrn@jsrn.dk>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************


from sage.functions.other import ceil, binomial
from sage.matrix.constructor import matrix
from sage.misc.misc_c import prod

####################### Linear algebra system solving ###############################
def _flatten_once(lstlst):
    r"""
    Flattens``lstlst`` only once and returns a generator.

    This is similar to Python's ``flatten`` method, except that here, if you
    provide a list of lists of lists (and so on), it returns a list of lists
    (and so on) and not a list.

    INPUT:

    - ``lstlst`` -- a list of lists.

    EXAMPLES::

    sage: from sage.coding.guruswami_sudan.interpolation import _flatten_once
    sage: ll = [[1,2], [3,4], [5,6]]
    sage: _flatten_once(ll) #random
    <generator object _flatten_once at 0x7fc1631cca50>
    """
    for lst in lstlst:
        for e in lst:
            yield e

def _monomial_list(maxdeg, l, wy):
    r"""
    Returns a list of the `(x,y)` powers of all monomials in `F[x,y]` whose
    (1,wy)-weighted degree is less than ``maxdeg`` and whose ``y-degree <= l``.

    INPUT:

    - ``maxdeg``, ``l``, ``wy`` -- integers.

    OUTPUT:

    - a list of pairs of integers.

    EXAMPLES::

        sage: from sage.coding.guruswami_sudan.interpolation import _monomial_list
        sage: _monomial_list(8, 5, 4)
        [(0, 0),
         (1, 0),
         (2, 0),
         (3, 0),
         (4, 0),
         (5, 0),
         (6, 0),
         (7, 0),
         (0, 1),
         (1, 1),
         (2, 1),
         (3, 1)]
    """
    monomials = []
    for y in range(0, l+1):
        for x in range(0,  ceil(maxdeg - y*wy)):
            monomials.append((x, y))
    return monomials

def _interpol_matrix_by_mons(points, s, monomials):
    r"""
    Returns a generator of the interpolation matrix whose nullspace gives the coefficients
    for all interpolation polynomials, given the list of monomials allowed.

    Its ``i``-th column will be the coefficients on the ``i``-th monomial
    in ``monomials``.

    INPUT:

    - ``points`` -- a list of integers, the interpolation points.

    - ``s`` -- an integer, the multiplicity parameter from Guruswami-Sudan algorithm.

    - ``monomials`` -- a list of monomials.

    EXAMPLES::

        sage: from sage.coding.guruswami_sudan.interpolation import _interpol_matrix_by_mons
        sage: points = [(0, 2), (1, 5), (2, 0), (3, 4), (4, 9), (5, 1), (6, 9), (7, 10)]
        sage: s = 1
        sage: monomials = [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (0, 1), (1, 1)]
        sage: _interpol_matrix_by_mons(points, s, monomials) #random
        <generator object _flatten_once at 0x7fb5ff8cce10>
    """
    n = len(points)
    def eqs_affine(x0,y0):
        r"""
        Make equation for the affine point x0, y0. Return a list of
        equations, each equation being a list of coefficients corresponding to
        the monomials in mons.
        """
        eqs = []
        for i in range(0, s):
            for j in range(0, s-i):
                eq = dict()
                for monomial in monomials:
                    ihat = monomial[0]
                    jhat = monomial[1]
                    if ihat >= i and jhat >= j:
                        icoeff = binomial(ihat, i)*x0**(ihat-i) \
                                    if ihat > i else 1
                        jcoeff = binomial(jhat, j)*(y0**(jhat-j)) \
                                    if jhat > j else 1
                        eq[monomial] = jcoeff*icoeff
                eqs.append([eq.get(monomial, 0) for monomial in monomials])
        return eqs
    return _flatten_once([ eqs_affine(*point) for point in points ])

def _interpol_matrix_problem(points, tau, parameters, wy):
    r"""
    Returns the linear system of equations which ``Q`` should be a solution to.

    This linear system is returned as a matrix ``M`` and a list of monomials ``monomials``,
    where a vector in the right nullspace of ``M`` corresponds to an
    interpolation polynomial `Q`, by the `i`'th element
    being the coefficient of the `i`'th monomial in ``monomials`` of `Q`.

    INPUT:

    - ``points`` -- a list of interpolation points.

    - ``tau`` -- an integer, the number of errors one wants to decode.

    - ``parameters`` -- (default: ``None``) a pair of integers, where:
        - the first integer is the multiplicity parameter of Guruswami-Sudan algorithm and
        - the second integer is the list size parameter.

    - ``wy`` -- an integer.

    EXAMPLES::

        sage: from sage.coding.guruswami_sudan.interpolation import _interpol_matrix_problem
        sage: points = [(0, 2), (1, 5), (2, 0), (3, 4), (4, 9), (5, 1), (6, 9), (7, 10)]
        sage: tau = 1
        sage: params = (1, 1)
        sage: wy = 1
        sage: _interpol_matrix_problem(points, tau, params, wy)
        (
        [     1      0      0      0      0      0      0      2      0      0      0      0      0]
        [     1      1      1      1      1      1      1      5      5      5      5      5      5]
        [     1      2      4      8     16     32     64      0      0      0      0      0      0]
        [     1      3      9     27     81    243    729      4     12     36    108    324    972]
        [     1      4     16     64    256   1024   4096      9     36    144    576   2304   9216]
        [     1      5     25    125    625   3125  15625      1      5     25    125    625   3125]
        [     1      6     36    216   1296   7776  46656      9     54    324   1944  11664  69984]
        [     1      7     49    343   2401  16807 117649     10     70    490   3430  24010 168070], [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1)]
        )
    """
    s, l = parameters[0], parameters[1]
    monomials = _monomial_list((len(points)-tau)*s, l, wy)
    M = matrix(list(_interpol_matrix_by_mons(points, s, monomials)))
    return (M, monomials)

def _construct_Q_from_matrix(M, monomials):
    r"""
    Returns a satisfactory ``Q`` polynomial given the interpolation matrix problem
    and the corresponding list of monomials.

    IMPUT:

    - ``M`` -- a matrix.

    - ``monomials`` -- a list of monomials.

    EXAMPLES::

        sage: from sage.coding.guruswami_sudan.interpolation import _construct_Q_from_matrix
        sage: from sage.coding.guruswami_sudan.interpolation import _interpol_matrix_problem
        sage: points = [(0, 2), (1, 5), (2, 0), (3, 4), (4, 9), (5, 1), (6, 9), (7, 10)]
        sage: tau = 1
        sage: params = (1, 1)
        sage: wy = 1
        sage: res = _interpol_matrix_problem(points, tau, params, wy)
        sage: M, monomials = res[0], res[1]
        sage: _construct_Q_from_matrix(M, monomials)
        4202026*x^6 - 5614235*x^5*y - 29351399*x^5 + 64635986*x^4*y + 41894587*x^4 - 273534229*x^3*y + 3*x^3 + 508264978*x^2*y + x^2 - 297101040*x*y + 2*x - 840*y + 1680
    """
    if M.nrows() >= M.ncols():
        raise Exception("More rows than columns! This matrix is not satisfactory.")
    Sp = M.right_kernel()
    sol = Sp.an_element()
    #TODO: Option to pick out minimal element?
    while sol.is_zero():
        # Picking out e.g. element 1 directly seems to run into an infinite
        # loop for large matrices.
        sol = Sp.random_element()
    # Construct the Q polynomial
    PF = M.base_ring()['x', 'y'] #make that ring a ring in <x>
    x, y = PF.gens()
    Q = sum([x**monomials[i][0] * y**monomials[i][1] * sol[i] for i in range(0, len(monomials))])
    print Q
    return Q

def construct_Q_linalg(points, tau, parameters, wy):
    r"""
    Returns an interpolation polynomial Q(x,y) for the given input.

    INPUT:

    - ``points`` -- a list of tuples ``(xi, yi)`` such that
      ``Q(xi,yi) = 0`` with multiplicity ``s``.

    - ``tau`` -- an integer, the number of errors one wants to decode.

    - ``parameters`` -- (default: ``None``) a pair of integers, where:
        - the first integer is the multiplicity parameter of Guruswami-Sudan algorithm and
        - the second integer is the list size parameter.

    - ``wy`` -- an integer.

    EXAMPLES::

        sage: from sage.coding.guruswami_sudan.interpolation import construct_Q_linalg
        sage: points = [(0, 2), (1, 5), (2, 0), (3, 4), (4, 9), (5, 1), (6, 9), (7, 10)]
        sage: tau = 1
        sage: params = (1, 1)
        sage: wy = 1
        sage: construct_Q_linalg(points, tau, params, wy)
        4202026*x^6 - 5614235*x^5*y - 29351399*x^5 + 64635986*x^4*y + 41894587*x^4 - 273534229*x^3*y + 3*x^3 + 508264978*x^2*y + x^2 - 297101040*x*y + 2*x - 840*y + 1680
    """
    return _construct_Q_from_matrix(
                *_interpol_matrix_problem(points, tau, parameters, wy))

####################### DEBUG ###############################

from sage.coding.guruswami_sudan.utils import apply_weights, remove_weights, LT, LP
from copy import copy

def module_row_reduction(M, i, j, pos):
    """Perform a row reduction with row j on row i, reducing position
    pos. If M[i,pos] has lower degree than M[j,pos], nothing is changed.
    Returns the multiple of row j used."""
    pow = M[i,pos].degree() - M[j,pos].degree()
    if pow < 0:
        return None
    coeff = -M[i, pos].leading_coefficient() / M[j, pos].leading_coefficient()
    x = M.base_ring().gen()
    multiple = x**pow*coeff
    M.add_multiple_of_row(i, j, multiple)
    return x**pow*coeff

def module_mulders_storjohann(M, weights=None, debug=0):
    """Reduce $M$ to weak Popov form using the Mulders--Storjohann
    algorithm (Mulders, T., and A. Storjohann. "On Lattice Reduction
    for Polynomial Matrices." Journal of Symbolic Computation 35, no.
    4 (2003): 377-401.).

    Handles column weights with only a slight possible penalty. The weights can
    be fractions, but cannot be floating points.

    If debug is True, then print some info."""
    if weights and len(weights) != M.ncols():
        raise ValueError("The number of weights must equal the number of columns")
    # initialise conflicts list and LP map
    LP_to_row = dict( (i,[]) for i in range(M.ncols()))
    conflicts = []
    for i in range(M.nrows()):
        lp = LP(M.row(i), weights=weights)
        ls = LP_to_row[lp]
        ls.append(i)
        if len(ls) > 1:
            conflicts.append(lp)
    iters = 0
    # while there is a conflict, do a row reduction
    while conflicts:
        lp = conflicts.pop()
        ls = LP_to_row[lp]
        i, j = ls.pop(), ls.pop()
        if M[i,lp].degree() < M[j, lp].degree():
            j,i = i,j

        module_row_reduction(M, i, j, lp)
        ls.append(j)
        lp_new = LP(M.row(i), weights=weights)
        if lp_new > -1:
            ls_new = LP_to_row[lp_new]
            ls_new.append(i)
            if len(ls_new) > 1:
                conflicts.append(lp_new)
        iters += 1
    return iters

def module_weak_popov(M, weights=None, debug=0):
    """Compute a (possibly column-weighted) weak Popov form of $M$.
    The weights can be any non-negative fractions."""
    return module_mulders_storjohann(M, weights=weights, debug=debug)

####################### END OF DEBUG ###############################

####################### Lee-O'Sullivan's method ###############################

def lee_osullivan_module(points, tau, (s,l), wy):
    r"""
    Returns the analytically straight-forward basis for the module containing
    all interpolation polynomials, as according to Lee and O'Sullivan

    EXAMPLES::

        sage: from sage.coding.guruswami_sudan.interpolation import lee_osullivan_module
        sage: points = [(0, 2), (1, 5), (2, 0), (3, 4), (4, 9), (5, 1), (6, 9), (7, 10)]
        sage: tau = 1
        sage: params = (1, 1)
        sage: wy = 1
        sage: PF = lee_osullivan_module(points, tau, params, wy)
        sage: print PF

    """
    F = points[0][0].parent()
    PF = F['x']
    x = PF.gens()[0]
    R = PF.lagrange_polynomial(points)
    G = prod(x - points[i][0] for i in range(0, len(points)))
    PFy = PF['y']
    y = PFy.gens()[0]
    ybasis = [(y-R)**i * G**(s-i) for i in range(0, s+1)] \
            + [y**(i-s) * (y-R)**s for i in range(s+1, l+1)]
    def pad(lst):
        return lst + [0]*(l+1-len(lst))
    modbasis = [pad(yb.coefficients(sparse=False)) for yb in ybasis]
    return matrix(PF, modbasis)

def construct_Q_lee_osullivan(points, tau, parameters, wy):
    r"""
    Returns an interpolation polynomial Q(x,y) for the given input.

    This interpolation method uses Lee-O'Sullivan's method.

    INPUT:

    - ``points`` -- a list of tuples ``(xi, yi)`` such that
      ``Q(xi,yi) = 0`` with multiplicity ``s``.

    - ``tau`` -- an integer, the number of errors one wants to decode.

    - ``parameters`` -- (default: ``None``) a pair of integers, where:
        - the first integer is the multiplicity parameter of Guruswami-Sudan algorithm and
        - the second integer is the list size parameter.

    - ``wy`` -- an integer.


    """
    # WARNING: CHANGE ALL OCCURENCES OF M TO Mnew AFTER row_reduced_form LINE!!!!!11
    from utils import apply_weights, remove_weights, LT
    s, l = parameters[0], parameters[1]
    F = points[0][0].parent()
    M = lee_osullivan_module(points, tau, (s,l), wy)
    weights = [i * wy for i in range(0,l+1)]
    apply_weights(M, weights)
    #Mnew = M.row_reduced_form(transformation=False, old_call=False)
    module_weak_popov(M, weights = None)
    # Construct Q as the element of the row with the lowest weighted degree
    degs = [(i, LT(M.row(i)).degree()) for i in range(0,l+1)]
    best = min(degs, key=lambda (i,d): d)[0]
    remove_weights(M, weights)
    Qlist = M.row(best)
    PFxy = F['x,y']
    xx, yy = PFxy.gens()
    Q = sum(yy**i * PFxy(Qlist[i]) for i in range(0,l+1))
    print Q
    return Q
