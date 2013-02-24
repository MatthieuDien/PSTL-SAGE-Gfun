from series import LazyPowerSeriesRing, LazyPowerSeries
from sage.categories.all import Fields
import sage.structure.parent_base


class FormalMultivariatePowerSeriesRing(LazyPowerSeriesRing):

# Inherited method : 
#  __cmp__(self,x)
#  _coerce_impl(self,x)



    def __init__(self, F, element_class = None, names = None):
        
        #Use Field to provide inverse method
        if not F in Fields():
            raise TypeError, "Argument F must be a Field."
        
        if names is None:
            names = 'z'
        
        self._element_class = element_class if element_class is not None else FormalMultivariatePowerSeries
        self._order = None
        # _name contains the equivalent of gens
        self._name = names

        #TODO : LazyPowerSeriesRing herits from Algebra that use old style parent class
        #see structure.parent.parent ans structure.parent.parent_base
        sage.structure.parent_base.ParentWithBase.__init__(self, F)

    def ngens(self):
        return len(self._name)

    def gens(self):
        return self._name

    def __repr__(self):
        return "Formal Multivariate Power Series Ring over %s"%self.base_ring()

    


class FormalMultivariatePowerSeries(LazyPowerSeries):
    pass
