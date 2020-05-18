from sage.arith.misc import xgcd, gcd, valuation
from sage.matrix.constructor import Matrix
from sage.misc.misc_c import prod

def Eij(i,j,N):
    #The matrix which just has one non-zero entry, 1, at (i+1,j+1).
    ei, ej = [], []
    for k in range(N):
        if k == i:
            ei.append([1])
        else:
            ei.append([0])
        if k == j:
            ej.append([1])
        else:
            ej.append([0])
    return Matrix(ei) * Matrix(ej).T

def Bd(d):
    return Matrix([[d,0],[0,1]])

def AL(N,S):
    r"""
    INPUT:

    - N - a positive integer
    - S - a maximal divisor of N or a set of primes

    OUPUT:

    - A matrix representing the partial Atkin-Lehner operator W_S

    """
    try:
        S = prod([p**(N.valuation(p)) for p in S])
    except TypeError:
        if gcd(S, N/S) > 1:
            S = S.prime_divisors()
            S = prod([p**(N.valuation(p)) for p in S])

    _, w, z = xgcd(S,N/S)
    z = -z
    return Matrix([[S, 1],[N*z, S*w]])

def complete_column(a,c,i = 1):
    """
    Completes a column a,c with gcd(a,c) = 1 to an SL_2(Z)-matrix.
    INPUT:
    - a - int, the top entry of the column.
    - c - int, the bottom entry of the column.
    - i - int.
    OUTPUT:
    - A matrix in SL_2(Z) with i-th column [a,c]
    """
    if gcd(a,c)>1:
        raise ValueError('Input needs to be coprime')
    _, d, b = xgcd(a, c)
    b = -b
    if i == 1:
        return Matrix([[a,b],[c,d]])
    elif i == 2:
        return Matrix([[-b,a],[-d,c]])

def complete_row(a,c,i = 1):
    """
    Completes a row a,c with gcd(a,c) = 1 to an SL_2(Z)-matrix.
    INPUT:
    - a - int, the top entry of the column.
    - c - int, the bottom entry of the column.
    - i - int.
    OUTPUT:
    - A matrix in SL_2(Z) with i-th column [a,c]
    """
    if gcd(a,c)>1:
        raise ValueError('Input needs to be coprime')
    return complete_column(a,c,i).T

def shift_cusp(gamma,t):
    r"""
    Returns gamma_2, delta such that B_t * gamma = gamma_2 * delta
    INPUT:
    - gamma - SL_2(Z) matrix
    - t - int, corresponds to the level shift B_t
    OUTPUT:
    - gamma, delta - gamma in SL_2(Z), delta triangular with B_t * gamma = gamma_2 * delta
    """
    a, c = gamma[0][0], gamma[1][0]
    gamma_2 = complete_column(a*t/gcd(a*t,c), c/gcd(a*t,c))
    delta = gamma_2**(-1) * Matrix([[t,0],[0,1]]) * gamma
    return gamma_2, delta

def moeb_trans(gamma,z):
    r"""
    Returns the Moebius transform of z under gamma.
    """
    a,b,c,d = gamma.list()
    if z == Cusp(Infinity):
        if c == 0:
            return Cusp(Infinity)
        else:
            return a/c
    elif c*z + d == 0:
        return Cusp(Infinity)
    else:
        return (a*z+b)/(c*z+d)

def aut_factor(gamma,z):
    _,_,c,d = gamma.list()
    return c*z+d
