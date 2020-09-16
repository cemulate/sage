r"""
Generalized Temperley--Lieb Algebras of Types A, B, D and H

The generalized Temperley--Lieb (TL) algebra of a Coxeter system, first defined
by Graham in [Graham1995]_, is a quotient of the Hecke algebra of the system by
an ideal generated by certain Kazhdan--Lusztig basis elements. The TL algebra
has several interesting bases indexed by the so-called fully commutative
elements of the Coxeter system, and for certain Coxeter systems the TL algebra
can be realized as a diagram algebra. For example, for Coxeter systems of type
`A` this recovers the well-known Temperley--Lieb algebra implemented in
``sage.combinat.diagrams_algebras``; in type `B` the diagrams have close
connections to the blob diagrams of ``sage.combinat.blob_algebra``. 

More generally, by a diagram realization of a generalized TL we mean an algebra
over a base ring `R` where a basis is given by certain decorated diagrams and
where multiplication is given by stacking of diagrams modulo certain
reductions; the decorations and reductions rules can be captured using a
"decoration algebra" isomorphic to a Verlinde algebra. This file implements the
diagram realizations of the generalized TL algebras of types A, B, D and H.

Authors:

- Chase Meadors, Tianyuan Xu (2020): Initial version

Acknowledgements
----------------

A draft of this code was written during an REU project at University of
Colorado Boulder. We thank Rachel Castro, Joel Courtney, Thomas Magnuson and
Natalie Schoenhals for their contribution to the project and the code.
"""
# ****************************************************************************
#  Copyright (C) 2020 Chase Meadors <Chase.Meadors at colorado.edu>,
#                     Tianyuan Xu   <Tianyuan.Xu at colorado.edu>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************
from sage.structure.list_clone import NormalizedClonableList
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent
from sage.misc.abstract_method import abstract_method
from sage.sets.family import Family
from sage.graphs.graph import Graph
from sage.functions.generalized import sign
from sage.rings.rational_field import QQ
from sage.rings.polynomial.all import PolynomialRing
from sage.rings.polynomial.laurent_polynomial_ring import LaurentPolynomialRing
from sage.algebras.free_algebra import FreeAlgebra
from sage.categories.sets_cat import Sets
from sage.categories.algebras_with_basis import AlgebrasWithBasis
from sage.combinat.free_module import CombinatorialFreeModule
from sage.combinat.root_system.coxeter_group import CoxeterGroup
from sage.combinat.root_system.coxeter_type import CoxeterType
from sage.combinat.diagram_algebras import TemperleyLiebDiagrams
from collections import deque
import math
import itertools


class DecoratedTemperleyLiebDiagram(NormalizedClonableList):
    r"""
    A decorated Temperley--Lieb (TL) diagram. 

    A TL diagram is a planar graph consisting of `2n` vertices `1, ..., n, -1,
    ...,-n'  and `n` edges or *arcs* which form a perfect matching of the graph
    for some positive integer `n`. We arrange the *positive* vertices 1, 2,
    ..., `n` from left to right on the top side of a rectangular frame and
    arrange the *negative* vertices -1, -2, ..., `-n` from left to right on the
    bottom side of the same frame. We call `n` the *order* of the diagram. An
    arc is called a *cap* if it connects two positive vertices, a *cup* if it
    connects two negative vertices, and *propogating* otherwise. 

    An arc in a TL diagram is call *left-exposed* if we can apply an plane
    isotopy to the diagram to make the arc touch the left side of the diagram's
    frame without crossing any other arc. A *decorated Temperley--Lieb diagram*
    is a TL diagram where each left-exposed arc may carry a decoration such as
    "the empty decoration" or "a dot"; each non-left-exposed arc is considered
    to carry "the empty decoration". These decorations will come from an
    associative algebra where they can be multiplied; the precise form of the
    decoration algebra and the decorations will depend on the Coxeter system
    the TL diagram is associated to. An arc which connects vertices `i, j` with
    `i<j` and carries decoration `d` is represented as a triple `(i,j,d)`; we
    set `d=1` for the empty decoration.
    """
    # Methods required as a subclass of NormalizedClonableList:
    def check(self):
        assert self in self.parent(), '{} not in {}'.format(str(self), str(self.parent())) 

    def normalize(self):
        # Sort each arc's endpoints, and then sort arcs in dictionary order.
        normalize_arc = lambda arc: (arc[0], arc[1], arc[2]) if arc[0] < arc[1] else (arc[1], arc[0], arc[2])
        noramlized_arcs = [normalize_arc(arc) for arc in self]
        self._set_list(sorted(noramlized_arcs))

    def _repr_(self):
        r"""
        #### mimic Travis' _repr_ in blob_algebra 
        """
        return '{' + ','.join('{' + ','.join(str(x) for x in arc) + '}' for arc in self) + '}'

    def to_graph(self):
        return Graph(list(self), weighted=True)

    def temperley_lieb_diagram(self):
        r"""
        ### mimic blob_algebra
        """
        return self.parent()._TLDiagrams([arc[:2] for arc in self])

    def get_arc_decoration(self, a, b):
        e = next((e for e in self if {e[0], e[1]} == {a, b}), None)
        if e is not None:
            return e[2]
        else:
            return None

    def a_value(self):
        r"""
        Return the number of caps, equivalently, the number of cups, in
        ``self``.

        The number is interesting because for a generalized TL algebra arising
        from a Coxeter system and a fully commutative element `w` in the
        system, the number of caps in the canonical diagram associated to `w`
        is often equal to `a(w)` where `a` denotes Lusztig's `a`-function.

        #### include a few examples
        """
        return len([e for e in self if e[0] > 0 and e[1] > 0])

    def get_left_exposed_propagating_edge(self):
        propagating = [arc for arc in self if sign(arc[0]) != sign(arc[1])]
        if len(propagating) == 0:
            return None
        else:
            return min(propagating, key=lambda arc: arc[0] if arc[0] > 0 else arc[1])

     


class DecoratedTemperleyLiebDiagrams(Parent, UniqueRepresentation):
    r"""
    The set of all decorated diagrams with a given order and decoration
    algebra.
    """
    def __init__(self, order, decoration_algebra):
        self._order = order
        self._decoration_algebra = decoration_algebra
        self._TLDiagrams = TemperleyLiebDiagrams(order)

        Parent.__init__(self, category=Sets())

    Element = DecoratedTemperleyLiebDiagram

    def order(self):
        r"""
        Return the order of the diagrams.
        """
        return self._order

    def __contains__(self, d):
        ### mimic blob_algebra, include lots of examples
        if not isinstance(d, DecoratedTemperleyLiebDiagram):
            return False
        if d.temperley_lieb_diagram() not in self._TLDiagrams:
            return False
        if any(arc[2] is not None and arc[2] not in self._decoration_algebra for arc in d):
            return False
        # Check left escaping
        for x, y in (arc[:2] for arc in d if arc[2] is not None):
            if x > 0:
                # (x, y) is a cup
                for arc in d:
                    if arc[1] < 0:
                        # arc is a cap
                        continue
                    elif arc[1] < x and arc[0] < 0:
                        # A propogating line to the left
                        return False
                    else:
                        # Note that arc[1] != x
                        if 0 < arc[0] < x:
                            # A nesting line
                            return False
            elif y < 0:
                # (x, y) is a cap
                for arc in d:
                    if arc[0] > 0:
                        # cup
                        continue
                    elif arc[0] > y and arc[1] > 0:
                        # A propogating line to the left
                        return False
                    else:
                        # Note that P[0] != y
                        if 0 > arc[1] > y:  # A nesting line
                            return False
            else:
                # Must be a propogating line
                if any(arc[0] < 0 and arc[1] > 0 and arc[1] < y for arc in d):
                    return False
        return True

    def _element_constructor_(self, arcs):
        return self.element_class(self, arcs)

    def _repr_(self):
        return ' '.join([
            'Generalized Temperley-Lieb diagrams',
            'of order {}'.format(self._order),
            'with decorations in {}'.format(str(self._decoration_algebra)) if self._decoration_algebra is not None else ''
        ])

class AbstractGeneralizedTemperleyLiebAlgebra(CombinatorialFreeModule):
    r"""
    Template for diagram realizations of generalized TL algebras of types A, B,
    and H, with a multiplication algorithm to be shared across all types.

    #### Include some examples that show how specific types (include two,
    perhaps) of TL algebras are
    created using this template, as well as some examples of diagram products.  

    """
    def __init__(self, order, R, decoration_algebra):
        r"""
        Initialize ``self``.

        #### include examples
        """
        self._decoration_algebra = decoration_algebra

        basis = DecoratedTemperleyLiebDiagrams(order, decoration_algebra)
        CombinatorialFreeModule.__init__(self, R, basis, category=AlgebrasWithBasis(R))

    def _element_constructor_(self, x):
        return self.basis()[self.element_class(self, x)]
    
    def _repr_term(self, x):
        # How basis elements are displayed in expressions
        return 'B[{}]'.format(str(x))

    # type-dependent methods to be specified in concrete types
    @abstract_method
    def algebra_generators(self):
        pass

    @abstract_method
    def _repr_(self):
        pass

    @abstract_method
    def decoration(self):
        pass

    @abstract_method
    def _process_loops(self, x):
        pass

    def one_basis(self):
        arcs = [(-i, i, 1) for i in range(1, self.basis().keys().order() + 1)]
        return self._indices.element_class(self._indices, arcs, check=False)
    
    def product_on_basis(self, b1, b2):
        r"""
        Compute the product `b1 * b2` of decorated TL diagrams `b1` and `b2`.

        Let `n` be the order of `b1` and `b2`. To obtain `b1 * b2`, first stack
        `b1` on top of `b2` and identity the bottom vertex `-i` in `b1` with
        the top vertex `i` in `b2` for all `1 \le i \le n`. Doing so results in
        a graph `D` with two types of vertices: the "outer" vertices that are
        in the top side of `b1` or the bottom side of `b2`, and the "inner" or
        "middle" vertices that come from the identification of a bottom vertex
        of `b1` with a top vertex of `b2`. Note that there are two possible
        kinds of arcs incident to two outer vertices in `D`: (1) the cups of
        `b2` and the caps of `b1`, which remain in `D` in the stacking, and (2)
        arcs connecting a bottom vertex `-i` in `b2` with a top vertex `j` in
        `b1`, obtained from a propogating arc of the form `\{-i,k\}` in `b2`
        and a propogating arc of the form `\{-k,j\}` in `b1` for some `1\le k
        \le n`. Finally, note that the stacking may result in loops formed out
        of a cup `\{i,j\}` in `b2` and a cup `\{-i,-j\}` in `b2`. 

        Next, we define the product `b1 * b2` in the diagram algebra to be the
        element `\delta^{l} \cdot d` where `\delta` is an element of the base
        ring `R` specified in the construction of the algbera, `l` is the
        number of loops in `D`, and `d` is the decorated TL diagram defined as
        follows: as a graph, its vertices are the `2n` outer vertices of `D`
        and its arcs are the arcs of Types (1) and (2); for decorations, every
        arc of Type (1) keeps its original decoration from `b1` or `b2`, while
        the decoration for an arc of Type (2) is defined to be the product, in
        the decoration algebra, of the decorations of the two arcs it arises
        from. 

        ####  Include Examples.
        """ 
        ##################################################
        # Step 1: Diagram stacking
        ##################################################
        
        t1, t2 = b1.to_graph(), b2.to_graph()
        union = t2.disjoint_union(t1)
        # union has vertices (0, v) for each v in t2, and (1, v) for each v in t1

        # Add edges from the "top" of t2 to the "bottom" of t1
        for v in t2:
            if v > 0:
                union.add_edge((0, v), (1, -v))

        # The new diagram
        result_arcs_and_loops = []

        for cc in union.connected_components():
            #### Can we get rid of the following? 
            # Don't care about "fake vertex" 0
            if (0, 0) in cc or (1, 0) in cc:
                continue

            # Vertices on the outer top or bottom
            outer_vertices = [x for x in cc if ((x[0] == 0 and x[1] < 0) or (x[0] == 1 and x[1] > 0))]
            # Edges that were in the original diagrams (that have edge labels)
            orig_edges = [e for e in union.edges() if e[0] in cc and e[1] in cc and e[0][0] == e[1][0]]

            # Multiply up all the edge labels in this connected component
            new_weight = 1
            for e in orig_edges:
                new_weight *= 1 if e[2] is None else e[2]

            if len(outer_vertices) == 0:
                # Represent loops as "arcs" with None as the endpoints to make things convenient
                result_arcs_and_loops.append((None, None, new_weight))
            else:
                # Add an edge between the original numbers of the outer vertices in the new graph, with new edge label.
                result_arcs_and_loops.append(tuple(e[1] for e in outer_vertices) + (new_weight,))
        
        ##################################################
        # PART 2: Expansion
        ##################################################
        
        # 'result_arcs_and_loops' is are now arcs/loops with labeled by
        # complex terms / polynomials in the decoration algebra.
        # We will distribute these local results "globally".
        
        # element is the linear combination of irreducible diagrams into which we will expand the results.
        element = self(0)

        right_pad = lambda l: l + [0] * (self.decoration().parent().degree() - len(l))
        coeff_lists = [right_pad(list(self._decoration_algebra(e[2]))) for e in result_arcs_and_loops]
        
        # Iterate over all possible choices of powers of d for every arc/loop
        for choice in itertools.product(range(self.decoration().parent().degree()), repeat=len(result_arcs_and_loops)):
            # For this choice, we want to construct a diagram with the edge ledges
            # being that simple power of d, prescribed by 'choice'
            
            # But first, how many of these diagrams should show up in the 'element'?
            # The product of the coefficients of these powers of d in 'result'.
            
            count = 1
            for i in range(len(result_arcs_and_loops)):
                count *= coeff_lists[i][choice[i]]
            
            # Bail
            if count == 0:
                continue
            
            # Now actually construct that diagram described earlier.
            
            labels = [self.decoration()**i for i in choice]
            arcs_and_loops = [e[:2] + (labels[i],) for (i, e) in enumerate(result_arcs_and_loops)]
            
            ##################################################
            # PART 3: Elimination rules
            ##################################################
            
            # The arcs and loops are now irreducible, i.e. they are labeled by pure powers of the decoration.
            # To obtain a proper diagram, we need to remove the loops and convert them into a multiplicative constant.
            
            arcs = [e for e in arcs_and_loops if e[0] is not None and e[1] is not None]
            loops = [e[2] for e in arcs_and_loops if e[0] == e[1] == None]
            # Perform type-specific logic to convert simple arcs and loops into 
            # a single term of the algebra (a multiple of a basis element indexed
            # by a proper diagram without loops).
            new_term = self._process_loops(arcs, loops)
            
            # Finally, add 'count' many of this term to 'element'
            
            element += self.base_ring()(count) * new_term
        
        return element

    # Inherit this member class to add some methods to elements of the algebra
    class Element(CombinatorialFreeModule.Element):
        def diagram(self):
            if len(self) != 1:
                raise ValueError("this is only defined for basis elements")
            return self.support_of_term()

        def _plot_basis(self, **kargs):
            import sage.plot.all as plot
            graphics = []

            # Expect a basis element:
            diagram = self.diagram()
            x_max = diagram.parent().order()

            # height of top border; calculated with bump_ry_delta in mind to comfortably
            # accommodate two opposing caps/cups of maximal width
            top = 1.45 + 0.2 * (max(x_max - 4, 0) // 2)
            # radius of dot decorations
            dot_radius = 0.05
            # The "base" vertical radius of the ellipse for a non-propagating arc, i.e.
            # the radius of a cap/cup with distance 1 between the bases.
            base_bump_ry = 0.5
            # Vertical radius of an arbitrary cap/cup is base plus this times the
            # difference of the endpoints.
            bump_ry_delta = 0.05
            # Padding around the whole drawing
            bound_margin = 0.5
            # Value affecting control points of bezier curve for propagating edges.
            bezier_control_ratio = 0.2

            use_square = kargs.get('use_square', False)
            dot_color = kargs.get('dot_color', 'blue')

            def pure_decoration_power(decoration):
                coefficients = list(self.parent().decoration().parent()(decoration))
                non_zero = [(j, c) for (j, c) in enumerate(coefficients) if c != 0]
                if len(non_zero) == 1:
                    (power, coeff) = non_zero[0]
                    if power > 0 and coeff == 1:
                        return power
                return None
            
            def decoration_graphic(point, kind):
                if kind == 'circle':
                    return plot.circle(point, dot_radius, facecolor=dot_color, fill=True, edgecolor='black')
                elif kind == 'square':
                    (x, y) = point
                    r = dot_radius
                    return plot.polygon([(x - r, y - r), (x - r, y + r), (x + r, y + r), (x + r, y - r)], color='white', fill=True, edgecolor='black')

            for (a, b, dec) in diagram:
                dec_type = 'circle'
                power = pure_decoration_power(dec)
                if power is None and use_square and dec == (2 * self.parent().decoration() - 1):
                    power = 1
                    dec_type = 'square'

                if sign(a) != sign(b):
                    # Propagating edge
                    x1, x2 = abs(a), abs(b)
                    # Normalization of tangles gaurantees a < b, so x1 is the
                    # x-coordinate of the bottom node and x2 of the top.
                    
                    if x1 == x2:
                        graphics.append(plot.line([(x1, 0), (x2, top)], color='black'))
                        if power is not None:
                            y_step = top / (power + 1)
                            for i in range(power):
                                y_loc = y_step * (i + 1)
                                graphics.append(decoration_graphic((x1, y_loc), dec_type))
                    else:
                        r = bezier_control_ratio
                        graphics.append(plot.bezier_path([[(x1, 0), (x1, (1-r) * top), (x2, r * top), (x2, top)]]))

                        if power is not None:
                            t_step = 1 / (power + 1)
                            for i in range(power):
                                t = t_step * (i + 1)
                                # This is the explicit parametric equation of the above cubic bezier curve:
                                x = -x1*(t - 1)**3 + 3*x1*(t - 1)**2*t - 3*x2*(t - 1)*t**2 + x2*t**3
                                y = -3*top*(r - 1)*(t - 1)**2*t - 3*top*r*(t - 1)*t**2 + top*t**3
                                graphics.append(decoration_graphic((x, y), dec_type))
                else:
                    # Cap/cup
                    neg = sign(a) < 0
                    x1, x2 = [abs(b), abs(a)] if neg else [a, b]
                    # Normalization of tangles gaurantees a < b, so x1, x2 are in order left to right.
                    y = 0 if neg else top
                    x_mid = abs(float(x1 + x2) / 2)
                    rx = x2 - x_mid
                    ry = base_bump_ry + bump_ry_delta * (x2 - x1)
                    sector = (0, math.pi) if neg else (math.pi, 2*math.pi)
                    graphics.append(plot.arc((x_mid, y), rx, ry, sector=sector, color='black'))

                    if power is not None:
                        x_step = float(x2 - x1) / (power + 1)
                        for i in range(power):
                            x = x1 + x_step*(i+1)
                            y_dist = (ry / rx) * math.sqrt(rx**2 - (x - x_mid)**2)
                            y = y_dist if neg else (top - y_dist)
                            graphics.append(decoration_graphic((x, y), dec_type))

            border_opts = {'color': 'black', 'linestyle': 'dotted', 'alpha': 0.5, 'thickness': 1.2}
            graphics.append(plot.line([(1 - bound_margin, 0), (1 - bound_margin, top)], **border_opts))
            graphics.append(plot.line([(1 - bound_margin, top), (x_max + bound_margin, top)], **border_opts))
            graphics.append(plot.line([(x_max + bound_margin, top), (x_max + bound_margin, 0)], **border_opts))
            graphics.append(plot.line([(x_max + bound_margin, 0), (1 - bound_margin, 0)], **border_opts))

            if 'coefficient' in kargs:
                c = kargs['coefficient']
                graphics.append(plot.text(str(c), (1 - bound_margin - 0.25, top / 2), fontsize='large'))

            if 'plus' in kargs and kargs['plus']:
                t = plot.text(str('+'), (x_max + bound_margin + 0.2, top / 2))
                graphics.append(t)

            if 'caption' in kargs:
                t = plot.text(kargs['caption'], (1 - bound_margin, top + 0.1), fontsize='large', color='black', horizontal_alignment='left')
                graphics.append(t)

            g = sum(graphics)
            g.axes(False)
            return g
        
        def plot(self, **kargs):
            from sage.plot.all import graphics_array
            graphics = []
            for (i, (diagram, coeff)) in enumerate(self):
                elt = self.parent().monomial(diagram)
                graphics.append(elt._plot_basis(coefficient=coeff, plus=(i != len(self) - 1), **kargs))
            
            return graphics_array([graphics])

def _u_diagram(diagrams, i, decoration):
    arcs = [(-j, j, None) for j in range(1, i)]
    arcs.append((-i, -(i+1), decoration))
    arcs.append((i, i+1, decoration))
    arcs.extend((-j, j, None) for j in range(i+2, diagrams.order() + 1))
    return diagrams.element_class(diagrams, arcs, check=False)

def GeneralizedTemperleyLiebAlgebra(family, order, R, delta):
    if family == 'A':
        return GeneralizedTemperleyLiebAlgebraA(order, R, delta)
    elif family == 'B':
        return GeneralizedTemperleyLiebAlgebraB(order, R, delta)
    elif family == 'H':
        return GeneralizedTemperleyLiebAlgebraH(order, R, delta)

class WithCanonicalBasisFamily():
    @abstract_method
    def _canonical_basis_index_set(self):
        pass

    @abstract_method
    def _canonical_basis_element(self, w):
        pass

    def canonical_basis(self):
        # TODO: Make some assertions about base_ring() and delta, etc., when is
        # this well-defined?
        fc_elements = self._canonical_basis_index_set()
        return Family(fc_elements, lambda w: self._canonical_basis_element(w), lazy=True)

class GeneralizedTemperleyLiebAlgebraA(AbstractGeneralizedTemperleyLiebAlgebra, WithCanonicalBasisFamily):
    def __init__(self, n, R, delta):
        self._delta = delta
        super().__init__(n, R, QQ)

    def _repr_(self):
        return 'Generalized Temperley-Lieb algebra of type A and order {} over {}'.format(self.basis().keys().order(), self.base_ring())

    def decoration(self):
        return QQ(1)
    
    def _process_loops(self, arcs, loops):
        # Loops are taken out as delta'
        m = 1
        for d in loops:
            m *= self._delta

        diagram = self._indices.element_class(self._indices, arcs, check=False)
        return m * self.basis()[diagram]
    
    def algebra_generators(self):
        return [self.monomial(_u_diagram(self.basis().keys(), i, None)) for i in range(1, self.basis().keys().order())]

    def _canonical_basis_index_set(self):
        return CoxeterGroup(['A', self.basis().keys().order() - 1]).fully_commutative_elements()

    def _canonical_basis_element(self, w):
        return self.prod([self.algebra_generators()[s-1] for s in w])

def _canonical_basis_expression_bh(F, w):
    def right_coset_decomposition_12(w):
        left = deque(w)
        right = deque() 
        three_found = False
        i = len(w) - 1

        while i > -1:
            s = w[i]
            if s == 1:
                right.appendleft(s)
                del left[i]
            elif s == 2:
                if three_found:
                    break
                else:
                    right.appendleft(s)
                    del left[i]
            elif s == 3:
                three_found = True
            i = i - 1
        return list(left), list(right)

    b_var = lambda s: F('b' + str(s))
    w = list(w)
    factors = deque([]) 
    one_on_right = False 
    # if the rightmost 2 in the parabolic part of a 12-coset decomposition has
    # a 1 on the right, then that 2 is internal.
    yielded =  list() 
    # if the leftmost letter in the parabolic part w_I 12-coset decomposition 
    # is a 1, we will 'yield' it to the left to be included in the next
    # 12-coset decomposition if and only if the 1 is not lateral, i.e., if and
    # only if w_I=1 or w_I=12---these are exactly the cases where no letter in 
    # w_I is required to keep the 1 to their left by the definition of right 
    # justified words.

    while w: 
        if w[-1] > 2:
            factors.appendleft(b_var(w.pop()))
        else: # i.e., once we come to a 1 or 2. 
            x = w + yielded
            x1, x2 = right_coset_decomposition_12(x)
            if x2[0]==2: 
            # this would imply there's no 1, hence no 2, to the left of x2
                if x2 == [2,1,2,1]:
                # the right 1 must have been yielded and hence not lateral
                    factors.appendleft(F('b2*b1*b2*b1-2*b2*b1')) 
                elif x2 == [2,1,2]:
                    # need to check if the rightmost 2 is internal or lateral
                    if one_on_right == False:
                        factors.appendleft(F('b2*b1*b2-b2'))
                    else:
                        factors.appendleft(F('b2*b1*b2-2*b2'))
                else: # x2=(2,) or x2=(2,1) (e.g., 2312)
                    factors.extendleft(b_var(s) for s in reversed(x2))
                factors.extendleft(b_var(s) for s in reversed(x1))
                return F.prod(factors)
            else: # i.e., if x2 starts with 1, the harder case
                # deal with x2 first:
                if x2 == [1,2,1,2]: # one_on_right must be false
                    factors.appendleft(F('b1*b2*b1*b2-2*b1*b2'))
                elif x2 == [1,2,1]: 
                # the right 1 must have been yielded from the last iteration
                    factors.appendleft(F('b1*b2*b1-b1'))
                    yielded = list() # cannot yield the left 1
                elif x2 == [1,2]: 
                    # check if the 2 is internal
                    if one_on_right == True: 
                    # then the 2 in x2 is internal and the 1 on its right
                    # hasn't been yielded because it's lateral, hence
                    # bilateral; 2 being internal also implies the 1 in x2 is
                    # lateral and should not be yielded
                        factors.appendleft(F('b1*b2-1'))
                    else: # the 2 is not internal, so yield the 1
                        factors.appendleft(F('b2'))
                        yielded = [1,]
                else: # i.e., if x2 = (1,)
                    yielded = [1,] # the only case factors is not updated
                one_on_right = True
            w = x1
    # in case the last yielded 1 hasn't been put into factors (e.g. 341231)
    if yielded == [1,]:
        factors.appendleft(F('b1'))
    return F.prod(factors)

class GeneralizedTemperleyLiebAlgebraB(AbstractGeneralizedTemperleyLiebAlgebra, WithCanonicalBasisFamily):
    def __init__(self, n, R, delta):
        self._delta = delta
        A = PolynomialRing(QQ, 'x')
        D = A.quotient(A.ideal(A('x^2 - x')), 'd')
        self._decoration = D.gens()[0]
        super().__init__(n, R, D)

    def _repr_(self):
        return 'Generalized Temperley-Lieb algebra of type B and order {} over {}'.format(self.basis().keys().order(), self.base_ring())

    def decoration(self):
        return self._decoration
    
    def _process_loops(self, arcs, loops):
        # Plain loops are taken out as delta, loops with 1 dot are taken out as delta/2
        m = 1
        for d in loops:
            if d == 1:
                m *= self._delta
            elif d == self.decoration():
                m *= self._delta / 2

        diagram = self._indices.element_class(self._indices, arcs, check=False)
        return m * self.basis()[diagram]
    
    def algebra_generators(self):
        return [self.monomial(_u_diagram(self.basis().keys(), i, (self.decoration() if i == 1 else None))) for i in range(1, self.basis().keys().order())]

    class Element(AbstractGeneralizedTemperleyLiebAlgebra.Element):
        def plot(self, **kargs):
            kargs['use_square'] = True
            kargs['dot_color'] = 'green'
            return super().plot(**kargs)

    def _canonical_basis_index_set(self):
        rank = self.basis().keys().order() - 1
        ctype = CoxeterType(['B', rank]).relabel(lambda s: rank - s + 1)
        return CoxeterGroup(ctype).fully_commutative_elements()

    def _canonical_basis_element(self, w):
        rank = self.basis().keys().order() - 1
        F = FreeAlgebra(self.base_ring(), ['b' + str(i) for i in range(1, rank + 1)])
        exp = _canonical_basis_expression_bh(F, w)
        return exp.subs({F.gens()[i]: (2 if i == 0 else 1) * self.algebra_generators()[i] for i in range(rank)})

class GeneralizedTemperleyLiebAlgebraH(AbstractGeneralizedTemperleyLiebAlgebra, WithCanonicalBasisFamily):
    def __init__(self, n, R, delta):
        self._delta = delta
        A = PolynomialRing(QQ, 'x')
        D = A.quotient(A.ideal(A('x^2 - x - 1')), 'd')
        self._decoration = D.gens()[0]
        super().__init__(n, R, D)

    def decoration(self):
        return self._decoration
    
    def _process_loops(self, arcs, loops):
        m = 1
        # Empty loops are taken out as delta, loops with one dot are taken out as 0
        for d in loops:
            if d == 1:
                m *= self._delta
            elif d == self.decoration():
                m = 0
                # End early
                return 0

        diagram = self._indices.element_class(self._indices, arcs, check=False)
        return m * self.basis()[diagram]
    
    def algebra_generators(self):
        return [self.monomial(_u_diagram(self.basis().keys(), i, (self.decoration() if i == 1 else None))) for i in range(1, self.basis().keys().order())]

    class Element(AbstractGeneralizedTemperleyLiebAlgebra.Element):
        def plot(self, **kargs):
            kargs['dot_color'] = 'orange'
            return super().plot(**kargs)

    def _canonical_basis_index_set(self):
        rank = self.basis().keys().order() - 1
        ctype = CoxeterType(['H', rank]).relabel(lambda s: rank - s + 1)
        return CoxeterGroup(ctype).fully_commutative_elements()

    def _canonical_basis_element(self, w):
        rank = self.basis().keys().order() - 1
        F = FreeAlgebra(self.base_ring(), ['b' + str(i) for i in range(1, rank + 1)])
        exp = _canonical_basis_expression_bh(F, w)
        return exp.subs({F.gens()[i]: self.algebra_generators()[i] for i in range(rank)})
