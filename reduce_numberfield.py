from sage.rings.complex_field import ComplexField, ComplexNumber
from sage.rings.number_field.number_field import CyclotomicField

CC = ComplexField()

def reduce_numberfield(a,K):
    r"""
    INPUT:

        a - an element that has the method minpoly. One should multiply a, so it becomes integral, otherwise the result might not be correct.
        K - number field, such that a is in K. If d is a number we set K = Q(zeta_d)

    OUTPUT:

        A representation of a in terms of zeta_d

    EXAMPLE:
        sage: zeta294 = CyclotomicField(294).gen()
        sage: a = 2/7*zeta294^77 - 6/7*zeta294^63 - 8/7*zeta294^56 + 5/7*zeta294^42 - 2/7*zeta294^28 - 4/7*zeta294^21 + 8/7*zeta294^7 + 3/7
        sage: reduce_cyclotomic(a*7,7)
        -2*zeta7^5 - 4*zeta7^4 - 6*zeta7^3 - 8*zeta7^2 - 3*zeta7 - 5

    """
    if K in ZZ:
        K = CyclotomicField(K)
    R = PolynomialRing(K, 'X')
    X = R.gen()
    candidates = [-p[0][0] for p in R(a.minpoly()).factor()]
    distances = [abs(CC(x)-CC(a)) for x in candidates]
    if min(distances)>.001:
        return 'Are you sure that a is in {}?'.format(K)
    return candidates[distances.index(min(distances))]
