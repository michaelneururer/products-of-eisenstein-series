import pdb

from sage.modular.cusps import Cusp
from sage.modular.arithgroup.congroup_gamma0 import Gamma0_class
from sage.rings.infinity import Infinity
from sage.rings.complex_field import ComplexField, ComplexNumber
from sage.rings.rational_field import RationalField
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.finite_rings.integer_mod import Mod
from sage.rings.big_oh import O
from sage.functions.transcendental import hurwitz_zeta
from sage.functions.generalized import sgn
from sage.functions.trig import cot
from sage.functions.other import factorial, ceil, floor
from sage.combinat.combinat import bernoulli_polynomial as ber_pol
from sage.matrix.constructor import Matrix
from sage.arith.misc import gcd, divisors
from sl2_operations import shift_cusp
from qexpansion import QExpansion

Gamma0 = Gamma0_class
pi = ComplexField().pi()
I = ComplexField().gen()
QQ = RationalField()
CC = ComplexField()


def hurwitz_hat(d, N, l, zetaN):
    r"""
    Computes the function zeta_hat(d/N, l) from Brunaults paper "Regulateurs
    modulaires via la methode de Rogers--Zudilin" as an element of Q(zetaN)
    at a non-positive integer l. We use the formula
    sum_{x in Z/NZ} zetaN**(xu) zeta(x/N, s) = N**s zeta_hat(u/N, s).
    INPUT:
    - d - int
    - N - int, positive int
    - l - int, non-positive integer
    OUTPUT:
    - an element of the ring Q(zetaN), equal to zeta_hat(d/N, l)
    """
    d = d%N
    k = 1-l
    if k < 1:
        raise ValueError, 'k has to be positive'
    if k == 1:
        s = -QQ(1)/QQ(2) # This is the term in the sum corresponding to x = 0
        s += sum([zetaN**(x*d)*(QQ(1)/QQ(2)-QQ(d)/QQ(N)+floor(QQ(d)/QQ(N)))
                    for d in range(1,N)])
    else:
        s = sum([-zetaN**(x*d)*(ber_pol(QQ(x)/QQ(N)-floor(QQ(x)/QQ(N)),k))/k
                    for x in range(N)])
    return N**(k-1) * s


def eisenstein_series_gammaN(cv, dv, N, k, Q, param_level=1, prec=10):
    r"""
    Computes the coefficient of the Eisenstein series for $\Gamma(N)$.
    Not intended to be called by user.
    INPUT:
    - cv - int, the first coordinate of the vector determining the \Gamma(N)
      Eisenstein series
    - dv - int, the second coordinate of the vector determining the \Gamma(N)
      Eisenstein series
    - N - int, the level of the Eisenstein series to be computed
    - k - int, the weight of the Eisenstein seriess to be computed
    - Q - power series ring, the ring containing the q-expansion to be computed
    - param_level - int, the parameter of the returned series will be
      q_{param_level}
    - prec - int, the precision.  The series in q_{param_level} will be truncated
      after prec coefficients
    OUTPUT:
    - an element of the ring Q, which is the Fourier expansion of the Eisenstein
      series
    """
    R = Q.base_ring()
    zetaN = R.zeta(N)
    q = Q.gen()

    cv = cv%N
    dv = dv%N

    if dv == 0 and cv == 0 and k == 2:
       raise ValueError("E_2 is not a modular form")

    if k == 1:
        if cv == 0 and dv == 0:
            raise ValueError("that shouldn't have happened...")
        elif cv == 0 and dv != 0:
            s = QQ(1)/QQ(2) * (1 + zetaN**dv)/(1 - zetaN**dv)
        elif cv != 0:
            s = QQ(1)/QQ(2) - QQ(cv)/QQ(N) + floor(QQ(cv)/QQ(N))
    elif k > 1:
        if cv == 0:
            s = hurwitz_hat(QQ(dv), QQ(N), 1-k, zetaN)
        else:
            s = 0
    for n1 in xrange(1, prec + 1): # this is n/m in DS
        for n2 in xrange(1, prec/n1 + 1): # this is m in DS
            if Mod(n1, N) == Mod(cv, N):
                s += n2**(k-1) * zetaN**(dv*n2) * q**(n1*n2)
            if Mod(n1, N) == Mod(-cv, N):
                s += (-1)**k * n2**(k-1) * zetaN**(-dv*n2) * q**(n1*n2)

    s += O(q**floor(prec))
    return s

def e_phipsi_alt(psi, phi, k, t=1, prec=5, mat=Matrix([[1, 0], [0, 1]]), base_ring=CC):
    r"""
    Computes the Eisenstein series attached to the characters psi, phi as
    defined on p129 of Diamond--Shurman, then hits it by mat \in \SL_2(\Z)
    INPUT:
     - psi, a primitive Dirichlet character
     - phi, a primitive Dirichlet character
     - k, an integer
     - t, an integer -- the shift
     - prec, the desired (relative?) precision
     - mat, a matrix - typically taking $i\infty$ to some other cusp
     - base_ring, a ring - the ring in which the modular forms are defined
    OUTPUT:
     - an instance of QExpansion
    """

    try:
        assert(QQ(psi(-1))*QQ(phi(-1)) == (-1)**k)
    except AssertionError:
        print("Parity of characters must match parity of weight")
        return None

    u = psi.level()
    v = phi.level()
    N = u * v

    zetaN = base_ring.zeta(N)
    Q = PowerSeriesRing(base_ring, 'q'+str(N))

    ser = 0
    mat, delta = shift_cusp(mat, t)
    #Find out the precision we need at the end.
    a, dd = delta[0][0], delta[1][1]
    a2, d2 = (a/dd).numerator(), (a/dd).denominator()
    for c in xrange(0, u):
        for d in xrange(0, v):
            for e in xrange(0, u):
                vgamma = Matrix([c*v, d+e*v]) * mat
                cvgamma, dvgamma = vgamma[0][0]%N, vgamma[0][1]%N
                cvgamma = cvgamma+N if cvgamma<0 else cvgamma
                dvgamma = dvgamma+N if dvgamma<0 else dvgamma

                if psi(c) != 0 and phi.bar()(d) != 0:
                    ser += base_ring(psi(c)) \
                           * base_ring(phi.bar()(d)) \
                           * eisenstein_series_gammaN(cvgamma,
                                                      dvgamma,
                                                      N,
                                                      k,
                                                      Q,
                                                      prec=N*prec*d2)
    gauss = 1 if phi.is_trivial() else phi.gauss_sum()
    ser *= u**(-k) / v * gauss * phi(-1)

    ser = QExpansion(level=N,
                      weight=k,
                      series=ser,
                      param_level=N).apply_triangular_matrix(delta)
    return ser
