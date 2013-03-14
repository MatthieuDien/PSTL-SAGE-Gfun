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

        #TODO : LazyPowerSeriesRing herits from Algebra that use old style parent class
        #see structure.parent.parent ans structure.parent.parent_base
        sage.structure.parent_base.ParentWithBase.__init__(self, R)
        #sage.structure.parent_gens.ParentWithGens.__init__(self,base=R,names=names) 

    def ngens(self):
        return self._ngens

    def gen(self,i=0):
        if i < 0 or i >= self._ngens:
            raise ValueError("Generator not defined")
        res = self.term(1,[int(j==i) for j in range(self._ngens)])
        res._name = self._names[i]
        return res

    def gens(self):
        return [self.gen(i) for i in range(self._ngens)]

    def __repr__(self):
        return "Formal Multivariate Power Series Ring over %s"%self.base_ring()

    #Inherits __cmp__ from LazyPowerSeriesRing
    #Inherits _coerce_impl from LazyPowerSeriesRing
    
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


    # Inherits zero_element from LazyPowerSeriesRing
    # Inherits identity_element from LazyPowerSeriesRing
    
    def term(self, r, n):
        

        if r == 0:
            res = self._new_initial(inf, Stream(const=[]))
            res._name = "0"
        else:
            if len(n)!=self._ngens or (True in [n[i]<0 for i in range(len(n))]) :
                raise ValueError, "values in n must be non-negative and len(n) need to be gen's number"
            BR = self.base_ring()
            s = [[]]*len(n)+[[(BR(r),n)]]+[[]]
            res = self._new_initial(sum(n), Stream(s))

            res._name= "%s"%repr(r)+''.join(["*%s^%s"%(self._names[i],n[i]) for i in range(self._ngens)])

        return res

    # Inherits _new_initial from LazyPowerSeriesRing
    
    # No methods for sum_gen and prod_gen (no very useful for the moment)
    
                                   

class FormalMultivariatePowerSeries(LazyPowerSeries):

    def __init__(self, A, stream=None, order=None, aorder=None, aorder_changed=True, is_initialized=False, name=None):
        LazyPowerSeries.__init__(self, A, stream=stream, order=order, aorder=aorder, aorder_changed=aorder_changed, is_initialized=is_initialized, name=name)
        self._zero = []

    def refine_aorder(self):
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
        n = len(self._stream)
        l = []
        if self._stream[0] != []:
            l = [(repr(self._stream[0][0][0]),1)]
        for i in range(1,n):
            t = self._stream[i]
            if t != [] :
                for e in t:
                    s=[]
                    for j in range(self.parent().ngens()):
                        if e[1][j] == 0:
                            pass
                        elif e[1][j] == 1:
                            s+=[self.parent()._names[j]]
                        else:
                            s+=['%s^%s'%(self.parent()._names[j],e[1][j])]
                    l += [('*'.join(s),e[0])]
        return l                          
            

    def __repr__(self):
        if self._name is not None:
            return self._name
        
        if self.is_initialized:
            n = len(self._stream)
            x = self.parent()._names
            l = repr_lincomb(self._get_repr_info())
        else:
            l = 'Uninitialized lazy power series'
        return l


    def _plus_gen(self,y,ao):

        for n in range(ao):
            yield []
        n = ao
        new_n = []
        while True:
            cy = y._stream[n]
            for (e,l) in self._stream[n]:
                c = (e,l)
                for i in range(cy):
                    if l == cy[i][1] :
                        c[0] += t[0]
                        cy = cy[0:i] + cy[i+1:]
                        break
                new_n.append(c)
            new_n += (cy)
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
