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
        return self._ngens

    def gen(self,i=0):
        if i < 0 or i >= self._ngens:
            raise ValueError("Generator not defined")
        if self._gens[i] == None :
            self._gens[i] = self.term(1,[int(j==i) for j in range(self._ngens)])
            self._gens[i]._name = self._names[i]
        return self._gens[i]

    def gens(self):
        return [self.gen(i) for i in range(self._ngens)]

    def __repr__(self):
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
        return self.term(0,[0]*self._ngens)

    def identity_element(self):
        return self.term(1,[0]*self._ngens)

    def term(self, r, n):
        

        if r == self.base_ring()(0):
            res = self._new_initial(inf, Stream(const=[]))
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
        return self._new(self._seq_gen, lambda *a : 0 )

    def composition(self,*args):
        if len(args) != self.parent().ngens() :
            raise ValueError, "you have to give %d arguments"%self.parent.ngens()
        return self._new(partial(self._compose_gen, args),lambda *a : self.aorder)

    __call__ = composition

    def _compose_gen(self,args,ao):   
        for f in args :
            assert f.coefficient(0) == []
        first_term = self.coefficient(0)
        new_serie = self.parent()(first_term[0][0]) if first_term != [] else self.parent().zero()
        yield new_serie.coefficient(0)
        n = 1
        while True :
            for (e,l) in self.coefficient(n) :
                new_serie += reduce(lambda a,b : a*b, map(lambda a,b: a.__pow__(b), args, l), e)
            yield new_serie.coefficient(n)
            n+=1

    def derivative(self,var):
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
