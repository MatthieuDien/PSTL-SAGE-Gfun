from series import LazyPowerSeriesRing, LazyPowerSeries

from stream import Stream, Stream_class
from series_order import  bounded_decrement, increment, inf, unk
from sage.rings.all import Integer, prod
from functools import partial
from sage.misc.misc import repr_lincomb, is_iterator

from sage.algebras.algebra import Algebra
from sage.algebras.algebra_element import AlgebraElement
import sage.structure.parent_base
from sage.categories.all import Rings


class FormalMultivariatePowerSeriesRing(Algebra):

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
        if i < 0 or n >= self._ngens:
            raise ValueError("Generator not defined")
        return self.term(1,[int(j==i) for j in range(self._ngens)])

    def gens(self):
        return [gen(i) for i in range(self._ngens)]

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
            if len(n)==self._ngens and (True in [n[i]<0 for i in range(len(n))]) :
                raise ValueError, "values in n must be non-negative and len(n) need to be gen's number"
            BR = self.base_ring()
            s = [[]]*len(n)+[[(BR(r),n)]]+[[]]
            res = self._new_initial(n, Stream(s))

            res._name= "%s"%repr(r)+''.join(["*%s^%s"%(gen(i),n[i]) for i in range(self._ngens)])

        return res

class FormalMultivariatePowerSeries(LazyPowerSeries):
    pass
