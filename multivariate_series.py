"""
Formal Multivariate Power Series

This files provides an implementation of Formal Multivariate Power
Series. The implementation is based on the LazyPowerSeriesRing and
LazyPowerSeries class. The internal data structure uses the stream class where
each case is a list of term of the same total degree. The terms are represented
by a 2-tuple with a coefficient from the base ring and a list of integer of
the same length that the number of variable, which is the monomonial
associated to the coefficient in the serie.
The mecanism is the same that for the Lazy Power Series.


This code is based on the work of Ralf Hemmecke and Martin Rubey's, developed
by Marguerite Zamansky and Matthieu Dien.
"""
#*****************************************************************************
#       Copyright (C) 2013 Matthieu Dien <matthieu.dien@gmail.com>, 
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************


from series import LazyPowerSeriesRing, LazyPowerSeries, uninitialized

from stream import Stream, Stream_class
from series_order import  bounded_decrement, increment, inf, unk
from sage.rings.all import Integer, prod
from functools import partial
from sage.misc.misc import repr_lincomb, is_iterator

from sage.algebras.algebra import Algebra
from sage.algebras.algebra_element import AlgebraElement
import sage.structure.parent_base
from sage.categories.all import Rings


class FormalMultivariatePowerSeriesRing(LazyPowerSeriesRing):

    def __init__(self, R, element_class = None, names = None):        
        #Make sure R is a ring with unit element
        if not R in Rings():
            raise TypeError, "Argument R must be a ring."
        try:
            z = R(Integer(1))
        except StandardError:
            raise ValueError, "R must have a unit element"

        #Take care of the names
        if names is None:
            names = ['z']
        
        self._ngens = len(names)
        self._element_class = element_class if element_class is not None else FormalMultivariatePowerSeries
        self._order = None
        self._names = names
        self._gens = [None]*self._ngens

        #TODO : LazyPowerSeriesRing herits from Algebra that use old style parent class
        sage.structure.parent_base.ParentWithBase.__init__(self, R)

    def ngens(self):
        """
        EXAMPLES::
        
                sage: R.<u,v,w,z> = FormalMultivariatePowerSeriesRing(QQ)
                sage: R.ngens()
                4
        """
        return self._ngens

    def gen(self,i=0):
        """
        EXAMPLES::

                sage: R.<u,v,w,z> = FormalMultivariatePowerSeriesRing(QQ)
                sage: R.gen(2)
                w

        TESTS::
                
                sage: R.<u,v,w,z> = FormalMultivariatePowerSeriesRing(QQ)
                sage: R.gen(4)
                Traceback (most recent call last):
                ...
                ValueError: Generator not defined
        """

        if i < 0 or i >= self._ngens:
            raise ValueError("Generator not defined")
        if self._gens[i] == None :
            self._gens[i] = self.term(1,[int(j==i) for j in range(self._ngens)])
            self._gens[i]._name = self._names[i]
        return self._gens[i]

    def gens(self):
        """
        EXAMPLES::

                sage: R.<u,v,w,z> = FormalMultivariatePowerSeriesRing(QQ)
                sage: R.gens()
                [u, v, w, z]
        """
        return [self.gen(i) for i in range(self._ngens)]

    def __repr__(self):
        """
        EXAMPLES::

                sage: R.<u,v,w,z> = FormalMultivariatePowerSeriesRing(QQ)
                sage: R
                Formal Multivariate Power Series Ring over Rational Field
        """
        return "Formal Multivariate Power Series Ring over %s"%self.base_ring()

    def __call__(self, x=None, order=unk):
        cls = self._element_class
        BR = self.base_ring()
        
        if x is None:
            res = cls(self, stream=None, order=unk, aorder=unk,
                      aorder_changed=True, is_initialized=False)
            res.compute_aorder = uninitialized
            return res

        #Must be changed because inheritance
        #Useless for the moment
        # if isinstance(x, LazyPowerSeries):
        #     x_parent = x.parent()
        #     if x_parent.__class__ != self.__class__:
        #         raise ValueError
            
        #     if x_parent.base_ring() == self.base_ring():
        #         return x
        #     else:
        #         if self.base_ring().has_coerce_map_from(x_parent.base_ring()):
        #             return x._new(partial(x._change_ring_gen, self.base_ring()), lambda ao: ao, x, parent=self)
        

        if hasattr(x, "parent") and BR.has_coerce_map_from(x.parent()):
            x = BR(x)
            return self.term(x, [0]*self._ngens)
        

        if hasattr(x, "__iter__") and not isinstance(x, Stream_class):
            x = iter(x)

        if is_iterator(x):
            x = Stream(x)

        if isinstance(x, Stream_class):
            aorder = order if order != unk else 0
            return cls(self, stream=x, order=order, aorder=aorder,
                       aorder_changed=False, is_initialized=True)

        elif not hasattr(x, "parent"):
            x = BR(x)
            return self.term(x, [0]*self._ngens)
            
        raise TypeError, "do not know how to coerce %s into self"%x


    def zero_element(self):
        """
        EXAMPLES::
                sage: R.<u,v,w,z> = = FormalMultivariatePowerSeriesRing(QQ)
                sage: R.zero_element()
                0
        """
        return self.term(0,[0]*self._ngens)

    def identity_element(self):
        """
        EXAMPLES::
                sage: R.<u,v,w,z> = = FormalMultivariatePowerSeriesRing(QQ)
                sage: R.identity_element()
                1
        """
        return self.term(1,[0]*self._ngens)

    def term(self, r, n):
        """
        EXAMPLES::
                sage: R.<u,v,w,z> = = FormalMultivariatePowerSeriesRing(QQ)
                sage: R.term(2,[1,4,0,2])
                2*u^1*v^4*w^0*z^2

        ::

                sage: R.term(2,[0,0,0,0])
                2

        ::

                sage: R.term(0,[1,9,0,3])
                0
        """
        if r == self.base_ring()(0):
            res = self._new_initial(inf, Stream([]))
            res._name = "0"
        elif sum(n) == 0:
            res = self._new_initial(0, Stream([[(r,n)],[]]))
            res._name = repr(r)
        else:
            if len(n)!=self._ngens or (True in [n[i]<0 for i in range(len(n))]) :
                raise ValueError, "values in n must be non-negative and len(n) need to be gen's number"
            BR = self.base_ring()
            s = [[]]*sum(n)+[[(BR(r),n)]]+[[]]
            res = self._new_initial(sum(n), Stream(s))

            res._name= "%s"%repr(r)+''.join(["*%s^%s"%(self._names[i],n[i]) for i in range(self._ngens)])

        return res

    # Inherits _new_initial from LazyPowerSeriesRing
    
    # No methods for sum_gen and prod_gen (no very useful for the moment)
    
                                   

class FormalMultivariatePowerSeries(LazyPowerSeries):

    def __init__(self, A, stream=None, order=None, aorder=None, aorder_changed=True, is_initialized=False, name=None):
        LazyPowerSeries.__init__(self, A, stream=stream, order=order, aorder=aorder, aorder_changed=aorder_changed, is_initialized=is_initialized, name=name)
        self._zero = []
        self._pows = None

    def refine_aorder(self):
        """
        Refines the approximate order of self as much as possible without
        computing any coefficients.

        EXAMPLES::
        
            sage: R.<u,v,w,z> = = FormalMultivariatePowerSeriesRing(QQ)
            sage: L = R([[]])
            sage: L.aorder
            0
            sage: L.refine_aorder()
            1
            sage: L.coeffcient(1)
            []
            sage: L.refine_aorder()
            sage: L.aorder
            Infinite series order

       ::

            sage: L = R([[],[],[(1,[1,1,0,0])],[]])
            sage: L.aorder
            0
            sage: L.coefficient(2)
            [(1,[1,1,0,0])]
            sage: L.refine_aorder()
            sage: L.aorder
            2

        """
        #If we already know the order, then we don't have
        #to worry about the approximate order
        if self.order != unk:
            return

        #aorder can never be infinity since order would have to
        #be infinity as well
        assert self.aorder != inf
        
        if self.aorder == unk or not self.is_initialized:
            self.compute_aorder()
        else:
            #Try to improve the approximate order
            ao = self.aorder
            c = self._stream
            n = c.number_computed()


            if ao == 0 and n > 0:
                while ao < n:
                    if self._stream[ao] == []:
                        self.aorder += 1
                        ao += 1
                    else:
                        self.order = ao
                        break

            #Try to recognize the zero series
            if ao == n:
                #For non-constant series, we cannot do anything
                if not c.is_constant():
                    return
                if c[n-1] == []:
                    self.aorder = inf
                    self.order  = inf
                    return

            # See ticket #14685 about LazyPowerSeries
            if self.order == unk:
                while ao < n:
                    if self._stream[ao] == []:
                        self.aorder += 1
                        ao += 1
                    else:
                        self.order = ao
                        break

            # if ao < n:
            #     self.order = ao
            
    
        if hasattr(self, '_reference') and self._reference is not None:
            self._reference._copy(self)

    def _get_repr_info(self):
        """
        EXAMPLES::
            sage: R.<u,v,w,z> = = FormalMultivariatePowerSeriesRing(QQ)
            sage: L = R([[],[(1,[1,0,0,0]),(3,[0,0,1,0])],[(1,[1,1,0,0]),(-5,[0,0,0,2])],[],[(1,[0,3,0,2])],[]])
            sage: L.coefficients(5)
            [[],
             [(1, [1, 0, 0, 0]), (3, [0, 0, 1, 0])],
             [(1, [1, 1, 0, 0]), (-5, [0, 0, 0, 2])],
             [],
             [(1, [0, 3, 0, 2])]]
            sage: L._get_repr_info()
            [('u', '1'), ('w', '3'), ('u*v', '1'), ('z^2', '-5'), ('v^3*z^2', '1')]
        """

        n = len(self._stream)
        l = []
        if self._stream[0] <> []:
            l = [(repr(self._stream[0][0][0]),1)]
        for i in range(1,n):
            t = self._stream[i]
            for e in t:
                s=[]
                for j in range(self.parent().ngens()):
                    if e[1][j] == 0:
                        pass
                    elif e[1][j] == 1:
                        s+=[self.parent()._names[j]]
                    else:
                        s+=['%s^%s'%(self.parent()._names[j],e[1][j])]
                l += [('*'.join(s),repr(e[0]))]
        return l                          
            

    def __repr__(self):
        """
        EXAMPLES::
            sage: R.<u,v,w,z> = = FormalMultivariatePowerSeriesRing(QQ)
            sage: L = R([[],[(1,[1,0,0,0]),(3,[0,0,1,0])],[(1,[1,1,0,0]),(-5,[0,0,0,2])],[],[(1,[0,3,0,2])],[]])
            sage: L.coefficients(5)
            sage: L
            u + 3*w + u*v + (-5)*z^2 + v^3*z^2
        """
        if self._name is not None:
            return self._name
        
        if self.is_initialized:
            n = len(self._stream)
            x = self.parent()._names
            l = repr_lincomb(self._get_repr_info())
        else:
            l = 'Uninitialized formal multivariate power series'
        return l

    def coefficient(self,*n):
        """
        EXAMPLES::
            sage: R.<u,v,w,z> = = FormalMultivariatePowerSeriesRing(QQ)
            sage: L = R([[],[(1,[1,0,0,0]),(3,[0,0,1,0])],[(1,[1,1,0,0]),(-5,[0,0,0,2])],[],[(1,[0,3,0,2])],[]])
            sage: L.coefficient(4)
            [(1,[0,3,0,2])]
        """
        if len(n) == 1:
            n=n[0]
            if self.get_aorder() > n:
                return self._zero
            assert self.is_initialized
            return self._stream[n]

        elif len(n) == self.parent().ngens():
            n=list(n)
            if self.get_aorder() > sum(n):
                return self.parent().base_ring()(0)
            assert self.is_initialized
            r=[e for (e,l) in self._stream[sum(n)] if l==n]
            return r[0] if r<>[] else self.parent().base_ring()(0)
        else:
            raise ValueError, "n must be an integer or an integer's list of size ngens()"

    def _plus_gen(self,y,ao):
        """
        EXAMPLES::
            sage: R.<u,v,w,z> = = FormalMultivariatePowerSeriesRing(QQ)
            sage: L = R([[],[(1,[1,0,0,0]),(3,[0,0,1,0])],[(1,[1,1,0,0]),(-5,[0,0,0,2])],[],[(1,[0,3,0,2])],[]])
            sage: K = u+v+w*z+w^2
            sage: G = L+K
            sage: G.coefficient(10); G
            []
            2*u + v + 3*w + w*z + w^2 + u*v + (-5)*z^2 + v^3*z^2
        """
        for n in range(ao):
            yield []
        n = ao
        while True:
            new_n = []
            cy = y._stream[n]
            for i in range(len(self._stream[n])):
                c = self._stream[n][i]
                for i in range(len(cy)):
                    if c[1] == cy[i][1] :
                        c = (c[0]+cy[i][0],c[1])
                        cy = cy[0:i] + cy[i+1:]
                        break
                if c[0] <> 0:
                    new_n.append(c)
            new_n += cy
            yield new_n
            n += 1
    
    def initialize_coefficient_stream(self, compute_coefficients):

        ao = self.aorder
        assert ao != unk

        if ao == inf:
            self.order = inf
            self._stream = Stream(const=[])
        else:
            self._stream = Stream(compute_coefficients(ao))

        self.is_initialized = True

    def _times_gen(self, y, ao):
        """
        EXAMPLES::
            sage: R.<u,v,w,z> = = FormalMultivariatePowerSeriesRing(QQ)
            sage: L = R([[],[(1,[1,0,0,0]),(3,[0,0,1,0])],[(1,[1,1,0,0]),(-5,[0,0,0,2])],[],[(1,[0,3,0,2])],[]])
            sage: K = u+v+w*z+w^2
            sage: G = L*K
            sage: G.coefficient(10); G
            []
            u^2 + 3*u*w + u*v + 3*v*w + u^2*v + (-5)*u*z^2 + u*v^2 + (-5)*v*z^2 + u*w*z + 3*w^2*z + u*w^2 + 3*w^3 + u*v*w*z + (-5)*w*z^3 + u*v*w^2 + (-5)*w^2*z^2 + u*v^3*z^2 + v^4*z^2 + v^3*w*z^3 + v^3*w^2*z^2
        """
        for n in range(ao):
            yield []

        n = ao
        while True:
            low = self.aorder
            high = n - y.aorder
            nth_coefficient = []

            #Handle the zero series
            if low == inf or high == inf:
                yield []
                n += 1
                continue

            for k in range(low, high+1):
                cx = self._stream[k]
                for i in range(len(cx)):
                    (h,t) = cx[i]
                    for j in range(len(y._stream[n-k])):
                        (e,l)=y._stream[n-k][j]
                        nl=list(map(lambda a,b:a+b,t,l))
                        already_in_list=False
                        for ii in range(len(nth_coefficient)):
                            if nth_coefficient[ii][1]==nl:
                                tt = nth_coefficient[ii][0]+e*h
                                if t <> 0:
                                    nth_coefficient[ii] = (tt,nl)
                                else :
                                    nth_coefficient[ii] = ()
                                already_in_list = True
                                break
                        if not(already_in_list) :
                            nth_coefficient+=[(h*e,nl)]
                        else :
                            if nth_coefficient[ii] == ():
                                nth_coefficient=nth_coefficient[:ii]+nth_coefficient[ii+1:]
            yield nth_coefficient
            n += 1

    def _pows_gen(self):

        A=self
        yield self.parent().identity_element()
        yield A
        while True:
            A=A*self
            yield A

    def __pow__(self,n):
        """
        EXAMPLES::
            sage: R.<u,v,w,z> = = FormalMultivariatePowerSeriesRing(QQ)
            sage: K = u+v+w*z+w^2
            sage: G = K^7
            sage: G.coefficient(20); G
            []
            u^7 + 7*u^6*v + 21*u^5*v^2 + 35*u^4*v^3 + 35*u^3*v^4 + 21*u^2*v^5 + 7*u*v^6 + v^7 + 7*u^6*w*z + 7*u^6*w^2 + 42*u^5*v*w*z + 42*u^5*v*w^2 + 105*u^4*v^2*w*z + 105*u^4*v^2*w^2 + 140*u^3*v^3*w*z + 140*u^3*v^3*w^2 + 105*u^2*v^4*w*z + 105*u^2*v^4*w^2 + 42*u*v^5*w*z + 42*u*v^5*w^2 + 7*v^6*w*z + 7*v^6*w^2 + 21*u^5*w^2*z^2 + 42*u^5*w^3*z + 21*u^5*w^4 + 105*u^4*v*w^2*z^2 + 210*u^4*v*w^3*z + 105*u^4*v*w^4 + 210*u^3*v^2*w^2*z^2 + 420*u^3*v^2*w^3*z + 210*u^3*v^2*w^4 + 210*u^2*v^3*w^2*z^2 + 420*u^2*v^3*w^3*z + 210*u^2*v^3*w^4 + 105*u*v^4*w^2*z^2 + 210*u*v^4*w^3*z + 105*u*v^4*w^4 + 21*v^5*w^2*z^2 + 42*v^5*w^3*z + 21*v^5*w^4 + 35*u^4*w^3*z^3 + 105*u^4*w^4*z^2 + 105*u^4*w^5*z + 35*u^4*w^6 + 140*u^3*v*w^3*z^3 + 420*u^3*v*w^4*z^2 + 420*u^3*v*w^5*z + 140*u^3*v*w^6 + 210*u^2*v^2*w^3*z^3 + 630*u^2*v^2*w^4*z^2 + 630*u^2*v^2*w^5*z + 210*u^2*v^2*w^6 + 140*u*v^3*w^3*z^3 + 420*u*v^3*w^4*z^2 + 420*u*v^3*w^5*z + 140*u*v^3*w^6 + 35*v^4*w^3*z^3 + 105*v^4*w^4*z^2 + 105*v^4*w^5*z + 35*v^4*w^6 + 35*u^3*w^4*z^4 + 140*u^3*w^5*z^3 + 210*u^3*w^6*z^2 + 140*u^3*w^7*z + 35*u^3*w^8 + 105*u^2*v*w^4*z^4 + 420*u^2*v*w^5*z^3 + 630*u^2*v*w^6*z^2 + 420*u^2*v*w^7*z + 105*u^2*v*w^8 + 105*u*v^2*w^4*z^4 + 420*u*v^2*w^5*z^3 + 630*u*v^2*w^6*z^2 + 420*u*v^2*w^7*z + 105*u*v^2*w^8 + 35*v^3*w^4*z^4 + 140*v^3*w^5*z^3 + 210*v^3*w^6*z^2 + 140*v^3*w^7*z + 35*v^3*w^8 + 21*u^2*w^5*z^5 + 105*u^2*w^6*z^4 + 210*u^2*w^7*z^3 + 210*u^2*w^8*z^2 + 105*u^2*w^9*z + 21*u^2*w^10 + 42*u*v*w^5*z^5 + 210*u*v*w^6*z^4 + 420*u*v*w^7*z^3 + 420*u*v*w^8*z^2 + 210*u*v*w^9*z + 42*u*v*w^10 + 21*v^2*w^5*z^5 + 105*v^2*w^6*z^4 + 210*v^2*w^7*z^3 + 210*v^2*w^8*z^2 + 105*v^2*w^9*z + 21*v^2*w^10 + 7*u*w^6*z^6 + 42*u*w^7*z^5 + 105*u*w^8*z^4 + 140*u*w^9*z^3 + 105*u*w^10*z^2 + 42*u*w^11*z + 7*u*w^12 + 7*v*w^6*z^6 + 42*v*w^7*z^5 + 105*v*w^8*z^4 + 140*v*w^9*z^3 + 105*v*w^10*z^2 + 42*v*w^11*z + 7*v*w^12 + w^7*z^7 + 7*w^8*z^6 + 21*w^9*z^5 + 35*w^10*z^4 + 35*w^11*z^3 + 21*w^12*z^2 + 7*w^13*z + w^14
        """
        if not isinstance(n, (int, Integer)) or n < 0:
            raise ValueError, "n must be a nonnegative integer"
        else:
            if self._pows is None :
                self._pows = Stream(self._pows_gen())
            return self._pows[n]

    def _seq_gen(self,ao):
        assert self.coefficient(0) == []
        yield [(self.base_ring()(1),[0]*self.parent()._ngens)]
        k=1
        while True:
            nth_coefficient = []
            for i in range(1,k+1):
                for (e,l) in self.__pow__(i).coefficient(k):
                    already_in_list=False
                    for ii in range(len(nth_coefficient)):
                        if l == nth_coefficient[ii][1]:
                            tt = e+nth_coefficient[ii][0]
                            if tt <> 0:
                                nth_coefficient[ii]=(tt,l)
                            else :
                                nth_coefficient[ii]=()
                            already_in_list = True
                            break
                    if not(already_in_list) :
                            nth_coefficient += [(e,l)]
                    else:
                        if nth_coefficient[ii] == ():
                            nth_coefficient=nth_coefficient[:ii]+nth_coefficient[ii+1:]
            yield nth_coefficient
            k +=1

    def seq(self):
        """
        EXAMPLES::
            sage: R.<u,v,w,z> = = FormalMultivariatePowerSeriesRing(QQ)
            sage: L = u.seq()
            sage: L.coeffcient(10); L
            [(1, [10, 0, 0, 0])]
            1 + u + u^2 + u^3 + u^4 + u^5 + u^6 + u^7 + u^8 + u^9 + u^10

        ::

            sage: L = (u+v^2+3*w*z).seq()
            sage: L.coefficient(4); L
            [(1, [0, 4, 0, 0]),
            (6, [0, 2, 1, 1]),
            (9, [0, 0, 2, 2]),
            (3, [2, 2, 0, 0]),
            (9, [2, 0, 1, 1]),
            (1, [4, 0, 0, 0])]
            1 + u + v^2 + 3*w*z + u^2 + 2*u*v^2 + 6*u*w*z + u^3 + v^4 + 6*v^2*w*z + 9*w^2*z^2 + 3*u^2*v^2 + 9*u^2*w*z + u^4

        """

        return self._new(self._seq_gen, lambda *a : 0 )

    def composition(self,*args):
        """
        EXAMPLES::
            
            sage: L = u+v^2+3*w*z+w^2
            sage: K = u+v^2
            sage: G = L(u,v,K,z)
            sage: G.coefficient(10); G
            []
            u + v^2 + 3*u*z + u^2 + 3*v^2*z + 2*u*v^2 + v^4
        """
        if len(args) != self.parent().ngens() :
            raise ValueError, "you have to give %d arguments"%self.parent.ngens()
        return self._new(partial(self._compose_gen, args),lambda *a : self.aorder)

    __call__ = composition

    def _compose_gen(self,args,ao):   
        for f in args :
            assert f.coefficient(0) == []
        first_term = self.coefficient(0)
        new_serie = None
        uninitialized = True
        if first_term != [] :
            uninitialized = False
            new_serie = self.parent()(first_term[0][0])
            yield new_serie.coefficient(0)
        else:
            yield []
        n = 1
        while True :
            for (e,l) in self.coefficient(n) :
                temp = reduce(lambda a,b : a*b, map(lambda a,b: a.__pow__(b), args, l), e)
                if uninitialized:
                    uninitialized = False
                    new_serie = temp
                else :
                    new_serie += temp
            yield new_serie.coefficient(n)
            n+=1

    def derivative(self,var):
        """
        EXAMPLES::
            
            sage: L = u+v^2+3*w*z+w^2
            sage: G = L.derivative(w)
            sage: G.coefficient(10); G
            []
            3*z + 2*w
        """
            
        return self._new(partial(self._diff_gen,var),bounded_decrement,self)

    def _diff_gen(self,var,ao):
        gens = self.parent().gens()
        if var not in gens:
            raise ValueError, "argument must be a generator"
        ind = gens.index(var)
        n=1
        while True:
            nth_coefficient = []
            for (c,l) in self.coefficient(n):
                if l[ind] != 0:
                    nl = l[:]
                    nl[ind] -= 1
                    nth_coefficient += [(c*l[ind],nl)]
            yield nth_coefficient
            n+=1
        

    def toPolynom(self,n):
        """
        Return a couple compoosed by a polynomial ring and the polynomial
        equal to the truncated series of degree n-1

        EXAMPLES::
            
           sage: 
           sage: L = u+v^2+3*w*z+w^2+u*v*z*w+u^2*v+w*z^4+v^6
           sage: (PolRing,PolL) = L.toPolynom(3)
           sage: PolL
           v^2 + w^2 + 3*w*z + u
           sage: PolRing
           Multivariate Polynomial Ring in u, v, w, z over Rational Field
        """        
        if n>0:
            from sage.rings.polynomial.all import PolynomialRing
            BR=self.parent().base_ring()
            R = PolynomialRing(BR,self.parent()._names)
            v = R.gens()
            pol = R(0)
            for i in range(n):
                l = self.coefficient(i)
                for (e,t) in l:
                    pol += e*reduce((lambda a,b:a*b),map((lambda a,b:a**b),v,t))
            return R,pol
        else:
            raise ValueError, "n must be a nonnegative integer"
