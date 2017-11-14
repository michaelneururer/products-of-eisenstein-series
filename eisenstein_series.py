import pdb

from sage.modular.cusps import Cusp
from sage.modular.arithgroup.congroup_gamma0 import Gamma0_constructor
from sage.modular.arithgroup.congroup_gamma1 import Gamma1_constructor
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
from sage.matrix.constructor import identity_matrix, Matrix
from sage.arith.all import gcd, divisors
from sl2_operations import shift_cusp, complete_column
from qexpansion import QExpansion

QQ = RationalField()
Gamma0 = Gamma0_constructor
Gamma1 = Gamma1_constructor

def cusps_of_gamma0(N):
    r"""
    INPUT:
     - N, an int
    OUTPUT:
     - list of representatives of cusps of Gamma0(N) given in Corollary 6.3.23 of [Cohen-Stromberg]. In particular they are of the form  a/b with b|N, b>0 and (a,N) = 1
    """
    cusps = []
    for b in divisors(N):
       for a0 in range(gcd(b,N/b)):
           if gcd([a0,b,N/b]) == 1:
               a = a0
               while True:
                   if gcd(a,N) == 1:
                       cusps.append(QQ(a)/QQ(b))
                       break
                   else:
                       a += gcd(b,N/b)
    return cusps

def find_correct_matrix(M,N):
    r"""
    Given a matrix M1 that maps infinity to a/c this returns a matrix M2 Matrix([[A,B],[C,D]]) that maps infinity to a Gamma0(N)-equivalent cusp A/C and satisfies, C|N, C>0, (A,N)=1 and N|B.
    It also returns T^n = Matrix([[1,n],[0,1]]) such that M2*T^n*M1**(-1) is in Gamma0(N).
    """
    a,b,c,d = map(lambda x: ZZ(x), M.list())
    if (c>0 and c.divides(N) and gcd(a,N) == 1 and b%N == 0):
        return M, identity_matrix(2)
    if c == 0:
        return Matrix([[1,0],[N,1]]), identity_matrix(2)
    cusps = cusps_of_gamma0(N)
    for cusp in cusps:
        if Cusp(QQ(a)/QQ(c)).is_gamma0_equiv(cusp,N):
            break
    A,C = cusp.numerator(),cusp.denominator()
    _, D, b = xgcd(A,N*C)
    M2 = Matrix([[A,-N*b],[C,D]])
    n = 0
    T = Matrix([[1,1],[0,1]])
    tmp = identity_matrix(2)
    while True:
        if N.divides((M2*tmp*M**(-1))[1][0]):
            return M2, tmp
        elif N.divides((M2*tmp**(-1)*M**(-1))[1][0]):
            return M2, tmp**(-1)
        tmp = tmp * T

def gauss_sum_corr(chi):
    #returns gauss_sum of a character unless it is the trivial character. In that case it returns 1.
    if chi.modulus() == 1:
        return 1
    return chi.gauss_sum()
#The following functions Pk, Qk, qm, Sk are helper functions to compute the Fourier coefficients of Eisenstein series at cusps.
def Pk(x,k):
    if k == 0:
        return 1
    else:
        return x*((x-1)*diff(Pk(x,k-1),x)-k*Pk(x,k-1))
def Qk(X,k):
    if X == 1:
        return bernoulli_polynomial(X,k)/QQ(k)
    P = PolynomialRing(QQ,'x')
    x = P.gen()
    g = Pk(x,k-1)/(x-1)**k
    return g(x=X)
def qm(f,k):
    if f == 1:
        return bernoulli_polynomial(1,k)/QQ(k)
    #Cohens function q(m) from page 15.
    P = PolynomialRing(QQ,'x')
    Q = P.quotient_by_principal_ideal(P.gen()**f-1,'t')
    t = Q.gen()
    #Polynomial in Lemma 5.3 time -f (so that it has integer coefficients. Corresponds to 1/(z-1)
    A = sum([(f-m-1)*t**m for m in range(f-1)])
    B = Pk(x,k-1)
    return (-1/f)**k * Q(B) * A**k
def Sk(chi,k):
    #Used to calculate constant term of Eisenstein series.
    M = chi.level()
    f = chi.conductor()
    chi_f = chi.primitive_character()
    pre_factor = (QQ(M)/QQ(f))**k
    for p in prime_divisors(QQ(M)/QQ(f)):
        pre_factor *= (1-chi_f(p)/QQ(p)**k)
    q = qm(f,k)
    s = 0
    for m in range(f):
        s+=chi_f.bar()(m)*q[m]
    return gauss_sum_corr(chi_f) * pre_factor * s

def e_phipsi(phi,psi, k, t=1, prec=5, mat=Matrix([[1, 0], [0, 1]]), base_ring=None):
    r"""
    Computes the Eisenstein series attached to the characters psi, phi as
    defined on p129 of Diamond--Shurman hit by mat \in \SL_2(\Z)
    INPUT:
     - psi, a primitive Dirichlet character
     - phi, a primitive Dirichlet character
     - k, int -- the weight
     - t, int -- the shift
     - prec, the desired absolute precision, can be fractional
     - mat, a matrix - typically taking $i\infty$ to some other cusp
     - base_ring, a ring - the ring in which the modular forms are defined
    OUTPUT:
     - an instance of QExpansion
    """
    chi2 = phi
    chi1 = psi
    try:
        assert(QQ(chi1(-1))*QQ(chi2(-1))==(-1)**k)
    except AssertionError:
        print("Parity of characters must match parity of weight")
        return None
    N1 = chi1.level()
    N2 = chi2.level()
    N = t*N1*N2
    mat2, Tn = find_correct_matrix(mat,N)
    #By construction gamma = mat2 * Tn * mat**(-1) is in Gamma0(N) so if E is our Eisenstein series we can evaluate E|mat = chi(gamma) * E|mat2*Tn.
    #Since E|mat2 has a Fourier expansion in qN, the matrix Tn acts as a a twist.
    #The point of swapping mat with mat2 is that mat2 satisfies C|N, C>0, (A,N)=1 and N|B and our formulas for the coefficients require this condition.
    A,B,C,D = mat2.list()
    gamma = mat2*Tn*mat**(-1)
    c_gamma = chi1(gamma[1][1])*chi2(gamma[1][1])
    if base_ring == None:
        Nbig = lcm(N,euler_phi(N1*N2))
        base_ring = CyclotomicField(Nbig,'zeta'+str(Nbig))
        zetaNbig = base_ring.gen()
        zetaN = zetaNbig**(Nbig/N)
    else:
        zetaN = base_ring.zeta(N)
    g = gcd(t,C)
    g1 = gcd(N1*g,C)
    g2 = gcd(N2*g,C)
    #Resulting Eisenstein series will have Fourier expansion in q_N**(g1g2)=q_(N/gcd(N,g1g2))**(g1g2/gcd(N,g1g2))
    Q = PowerSeriesRing(base_ring, 'q'+str(N/gcd(N,g1*g2)))
    qN = Q.gen()
    zeta_Cg = zetaN**(N/(C/g))
    zeta_tmp = zeta_Cg**(inverse_mod(-A*ZZ(t/g),C/g))
    #Calculating a few values that will be used repeatedly
    chi1bar_vals = [base_ring(chi1.bar()(i)) for i in range(N1)]
    cp_list1 = [i for i in range(N1) if gcd(i,N1)==1]
    chi2bar_vals = [base_ring(chi2.bar()(i)) for i in range(N2)]
    cp_list2 = [i for i in range(N2) if gcd(i,N2)==1]

    #Computation of the Fourier coefficients
    ser = 0
    for n in range(1,ceil(prec*N/QQ(g1*g2))+1):
        f = 0
        for m in divisors(n)+map(lambda x:-x,divisors(n)):
            a=0
            for r1 in cp_list1:
                b = 0
                if ((C/g1)*r1 - QQ(n)/QQ(m))%((N1*g)/g1) == 0:
                    for r2 in cp_list2:
                        if ((C/g2)*r2 - m)%((N2*g)/g2) == 0:
                            b += chi2bar_vals[r2]*zeta_tmp**((n/m-(C/g1)*r1)/((N1*g)/g1)*(m-(C/g2)*r2)*((N2*g)/g2))
                    a += chi1bar_vals[r1]*b
            a *= sign(m)*m**(k-1)
            f += a
        f*= zetaN**(inverse_mod(A,N)*(g1*g2)/C*n)
        #The additional factor zetaN**(n*Tn[0][1]) comes from the twist by Tn
        ser += zetaN**(n*g1*g2*Tn[0][1])*f*qN**(n*((g1*g2)/gcd(N,g1*g2)))

    #zk(chi1, chi2, c)
    gauss1 = base_ring(gauss_sum_corr(chi1.bar()))
    gauss2 = base_ring(gauss_sum_corr(chi2.bar()))
    zk = 2*(N2*t/QQ(g2))**(k-1)*(t/g)*gauss1*gauss2
    #Constant term
    if N1.divides(C) and ZZ(C/N1).divides(t) and gcd(t/(C/N1),N1) == 1:
        ser += (-1)**(k-1)*gauss2/QQ(N2*(g2/g)**(k-1))*chi1bar_vals[(-A*t/g)%N1]*Sk(chi1.bar().extend(N1*N2).base_extend(base_ring)*chi2.extend(N1*N2).base_extend(base_ring),k)
    elif k==1 and N2.divides(C) and ZZ(C/N2).divides(t) and gcd(t/(C/N2),N2)==1:
        ser += gauss1/QQ(N1)*chi2bar_vals[(-A*t/g)%N2]*Sk(chi1.extend(N1*N2).base_extend(base_ring)*chi2.bar().extend(N1*N2).base_extend(base_ring),k)
    return QExpansion(N,k,2/zk*c_gamma*ser+O(qN**floor(prec*N/gcd(N,g1*g2))),N/gcd(N,g1*g2))
