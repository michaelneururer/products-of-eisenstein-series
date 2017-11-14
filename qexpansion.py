from sage.rings.integer_ring import IntegerRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.big_oh import O
from sage.arith.all import lcm
from sage.rings.complex_field import ComplexField

ZZ = IntegerRing()

class QExpansion:
    """
    A class for q-expansions of modular forms
    """

    def __init__(self, level, weight, series, param_level):
        self.level = level
        self.weight = weight
        self.series = series
        self.param_level = param_level
        self.prec = self.series.prec

    def __eq__(self,other):
        if isinstance(other, QExpansion):
            if self.series == other.series and self.param_level == other.param_level:
                return True
        else:
            return False

    def __repr__(self):
        print(self.series)
        return ''

    def __mul__(self, other):
        if isinstance(other, QExpansion):
            common_param_level = lcm(self.param_level, other.param_level)
            self.pad(common_param_level)
            other.pad(common_param_level)

            return QExpansion(level = self.level, 
                              weight = 2*self.weight, 
                              series = self.series * other.series, 
                              param_level = self.param_level)
        
        R = self.series.base_ring()
        if other in R:
            return QExpansion(level = self.level,
                              weight = self.weight,
                              series = other * self.series,
                              param_level = self.param_level)

        raise ValueError

    __rmul__ = __mul__
    
    def __div__(self, scalar):
        return self.__mul__(1/scalar)

    __rdiv__= __div__

    def __add__(self, other):
        if isinstance(other, QExpansion):
            common_param_level = lcm(self.param_level, other.param_level)
            self.pad(common_param_level)
            other.pad(common_param_level)

            return QExpansion(level = self.level,
                              weight = self.weight,
                              series = self.series + other.series,
                              param_level = self.param_level)
        
        raise ValueError

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-1)*other


    def __getitem__(self, i):
        return self.series[i]

    def __len__(self):
        return len(self.series.padded_list())
    
    def padded_list(self):
        return self.series.padded_list()

    def base_ring(self):
        return self.series.base_ring()

    def pad(self, target_param_level):
        """
        When constructed the q-expansions are in the default parameter $q_N$,
        where $N$ is the level of the form.  When taking products, the 
        parameters should be in $q_{N'}$, where $N'$ is the target level.
        This helper function peforms that renormalization by padding with zeros.
        """
        try:
            assert(target_param_level % self.param_level == 0)
        except AssertionError:
            print("target parameter level should be a multiple of current parameter level")
            return

        shift = int(target_param_level / self.param_level)
        R = self.series.base_ring()
        Q = PowerSeriesRing(R, 'q'+str(target_param_level))
        qN = Q.gen()
        s = 0
        for i in xrange(self.series.prec() * shift):
            if i % shift == 0:
                s += self.series[int(i/shift)] * qN**i
            else:
                s += 0 * qN**i
        s += O(qN**(self.series.prec() * shift))
        self.series = s
        self.param_level = target_param_level

    def prune(self, tar_param_level):
        """
        Prunes terms from the q-expansion to return a series in the desired
        parameter
        """
        try:
            assert(self.param_level % tar_param_level == 0)
        except AssertionError:
            print("target parameter level should be a divsor of current parameter level")
            return

        R = self.series.base_ring()
        Q = PowerSeriesRing(R, 'q'+str(tar_param_level))
        q = Q.gen()

        s = 0
        for i in xrange(self.series.prec() * tar_param_level // self.param_level):
            s += self.series[i * (self.param_level // tar_param_level)] * q**i
        s += O(q**(self.series.prec() * tar_param_level // self.param_level))
        self.series = s
        self.param_level = tar_param_level


    def apply_triangular_matrix(self, delta):
        """
        If self is a q-expansion and q = exp(2*pi*I*tau), then applying a 
        triangular matrix [[a,b],[0,d]] to tau gives a well-defined 
        q-expansion as long as the base ring contains zeta_d. 
        Warning: The correct slash-action would also multiply with det(delta)^k/2 but we carefully avoid that in all applications of apply_triangular_matrix.
        """
        R = self.series.base_ring()
        a, b, d = delta[0][0], delta[0][1], delta[1][1]
        """
        Reduce the fraction a/d
        """
        a2, d2 = (a/d).numerator(), (a/d).denominator()
        b2, d3 = (b/d).numerator(), (b/d).denominator()
        zetad = R.zeta(d3*self.param_level)
        Q = PowerSeriesRing(R, 'q'+str(self.param_level*d2))
        qNd = Q.gen()
        s = 0
        for i in xrange(self.series.prec()):
            s += self.series[i] * zetad**(i*b2) * qNd**(i*a2)
        s = s + O(qNd**(self.series.prec()))
        s = s * d**(-self.weight)
        return QExpansion(self.level*d2, self.weight, s, self.param_level*d2)
