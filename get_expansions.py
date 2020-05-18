from eisenstein_series import e_phipsi
from sl2_operations import complete_column, shift_cusp, AL, Bd
from products import product_space
from sage.modular.dims import sturm_bound
from sage.modules.free_module_element import vector
from sage.modular.arithgroup.congroup_gamma0 import Gamma0_constructor
from sage.modular.arithgroup.congroup_gamma1 import Gamma1_constructor
from sage.modular.cusps import Cusp
from sage.modular.dirichlet import DirichletGroup
from sage.rings.infinity import Infinity
from sage.rings.rational_field import RationalField
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.number_field.number_field import CyclotomicField
from sage.misc.cachefunc import CachedFunction
from sage.arith.all import lcm, euler_phi

product_space = CachedFunction(product_space)

QQ = RationalField()
Gamma0 = Gamma0_constructor
Gamma1 = Gamma1_constructor

load('eisenstein_series.py')

def lin_comb(f, weights= False, base_ring=None, hom=None, verbose=False):
    r"""
    Computes the a representation of a modular form f as a linear combination
    of products of Eisenstein series.
    INPUT:
    - f, a modular form
    - weights, list - a list of allowed weights for the Eisenstein series.
    - base_ring, a ring over which computations will be done.
    - hom, a homomorphism of the base ring of f into base_ring.
    OUTPUT:
    - sol, ind - A vector of coefficients for the linear combination and a
      list of indices to identify which product belongs to which coefficient.
      If an index has the form [k, i, j, t1], then it corresponds to Eisenstein
      series E_k^{\phi,\psi,t1}, where phi = DirichletGroup(N)[i] and
      psi = DirichletGroup(N)[j].  If an index has the form
      [l, k-l, i, j, t1, t2, t], then it corresponds to the product
      E_l^{\phi,\psi,t1 t} * E_{k-l}^{\phi.bar(),\psi.bar(),t2 t}
    """
    chi = f.character()
    k = f.weight()

    if verbose:
        print('Setting up product space...')
    products, indexlist = product_space(chi,
                                        k,
                                        weights=weights,
                                        base_ring=base_ring, verbose=verbose)
    if verbose:
        print('Done: There are {} products with {} coefficients each.'.
               format(len(indexlist),len(products.rows()[0])))

    prec = sturm_bound(chi.level(), k) + 1
    K = products.base_ring()
    solution = []
    B = f.base_ring()
    if B == QQ:
        coeffs = [0] + f.coefficients(prec)
    else:
        if base_ring==None:
            base_ring = K.composite_fields(B,'c')[0]
        if hom==None:
            hom = B.Hom(L)[0]
        coeffs = [0] + map(hom, f.coefficients(prec))
        hom = K.Hom(L)[0]
    try:
        solution = products.T.solve_right(vector(coeffs))
    except ValueError:
        print("Could not write form as lin. comb. of Eisenstein series and products of Eisenstein series")
        return None

    return solution, indexlist

def AL_eigenvalue(f, S, base_ring=None, verbose = False,eis_alt=False):
    r"""
    Computes the Atkin-Lehner eigenvalue of an eigenform f. Warning: This function does not check if the input f is such an eigenform.
    INPUT:

    - ``f``, a modular form
    - S - a maximal divisor of N or a set of primes
    - base_ring - a ring that contains the coefficients of f and the root of unity zeta_{lcm(N,phi(N))}
    - ``verbose``, boolean - If True there will be text describing every step of the calculation

    OUTPUT:

    - The q-expansion of f at the cusp
    """
    K = f.base_ring()
    i = 1
    #Get first non-zero coefficient of f
    while True:
        if f.coefficient(i) != 0:
            f1 = f.coefficient(i)
            break
        i+=1

    N = f.level()
    k = f.weight()
    try:
        NS = prod([p**(N.valuation(p)) for p in S])
    except TypeError:
        if gcd(S, N/S) > 1:
            S = S.prime_divisors()
            S = prod([p**(N.valuation(p)) for p in S])
        NS = S
    W = AL(N, S)*Matrix([[1/QQ(NS),0],[0,1]])
    s = get_expansion(f,prec = QQ(i)/QQ(NS)+2, cusp = W, base_ring=base_ring, verbose = verbose, eis_alt=eis_alt)*NS**(k/2)
    return s[i*NS/s.param_level] * K(f1)**(-1)

def get_expansion(f, prec=2, mat=Cusp(Infinity), group=None, base_ring=None, verbose=False, eis_alt=False):
    r"""
    Computes the Fourier expansion of a modular form f of level N at an
    arbitrary cusp.
    INPUT:

    - ``f``, a modular form
    - ``prec``, the desired absolute precision, can be fractional. The expansion will be up to O(q_w^(floor(w*prec))), where w is the width of the cusp.
    - ``mat``, a matrix or a cusp. The result will be the Fourier expansion of f|mat. If mat is a cusp, then get_expansion chooses a matrix g in SL_2(Z) that maps infinity to mat.
    - ``group``, string or None -- the congruence group of f either 'Gamma0' or 'Gamma1'
    - base_ring - a ring that contains the coefficients of f and the root of unity zeta_{lcm(N,phi(N))}
    - ``verbose``, boolean - If True there will be text describing every step of the calculation
    - ``eis_alt``, boolean = If True an alternative version of the eisenstein_series will be used in the calculation. This is merely for testing purposes.

    OUTPUT:

    - The q-expansion of f at the cusp

    EXAMPLES:
    ::

        sage: f11 = Newforms(11)[0]
        sage: get_expansion(f11, prec = 5, mat = Infinity)
        q1 - 2*q1^2 - q1^3 + 2*q1^4 + O(q1^5)
        sage: get_expansion(f11, prec = 8/11, mat = 0)
        -1/11*q11 + 2/11*q11^2 + 1/11*q11^3 - 2/11*q11^4 - 1/11*q11^5 - 2/11*q11^6 + 2/11*q11^7 + O(q11^8)

        sage: f49 = Newforms(49)[0]
        sage: get_expansion(f49, prec = 2, mat = 1/7, verbose = False) #This might take a minute. Set verbose to True if you want updates on the status of the calculation
        (2/7*zeta294^77 - 6/7*zeta294^63 - 8/7*zeta294^56 + 5/7*zeta294^42 - 2/7*zeta294^28 - 4/7*zeta294^21 + 8/7*zeta294^7 + 3/7)*q1 + O(q1^2)

    """
    if verbose:
        print('Finding coefficients of linear combination...')
    sol, ind = lin_comb(f, verbose=verbose)
    if verbose:
        print('{} coefficients are non-zero'.
              format(len([s for s in sol if s != 0])))
    if group == None:
        group = f.group()

    return combine_sol(f.level(),
                       sol,
                       ind,
                       prec=prec,
                       mat=mat,
                       group=group,
                       base_ring=base_ring,
                       verbose=verbose,
                       eis_alt=eis_alt)


def combine_sol(N, coeffs, ind, prec=2, mat=Cusp(Infinity), group='Gamma0', base_ring=None, verbose = False, eis_alt=False, cmplx_embedding=None):
    r"""
    INPUT:
     - N, an int -- the level of the forms
     - coeffs, an array of elts of the base ring -- gives the coefficients
       for the linear combination of Eisenstein series or products of
       Eisenstein series.
     - ind, an array -- has same length as coeffs, entries of ind are parameters
      describing the Eisenstein series or product of Eisenstein series
     - prec, the desired absolute precision, can be fractional. The expansion will be up to O(q_w^(floor(w*prec))), where w is the width of the cusp.
     - ``mat``, a matrix or a cusp. The result will be the Fourier expansion of f|mat. If mat is a cusp, then get_expansion chooses a matrix g in SL_2(Z) that maps infinity to mat.
     - group, a string or an arithgroup -- can be either Gamma0 or Gamma1
     - base_ring - a ring that contains the coefficients of f and the root of unity zeta_{lcm(N,phi(N))}
     - verbose, a boolean -- set true to get information about progress through the
       computation
    OUTPUT:
     - the Fourier expansion at the given cusp
    """
    if eis_alt:
        load('eisenstein_series_alternative.py')
    # First step: Convert cusp into matrix
    if group == 'Gamma0':
        group = Gamma0(N)
        tp = 0
    elif group == 'Gamma1':
        group = Gamma1(N)
        tp = 1
    elif group == Gamma0(N):
        tp = 0
    elif group == Gamma1(N):
        tp = 1
    try:
        cusp = Cusp(mat)
        cusps = group.cusps()
        for c in cusps:
            if tp == 0:
                if c.is_gamma0_equiv(cusp, N):
                    mat = c
                    break
            if tp == 1:
                if c.is_gamma1_equiv(cusp, N):
                    mat = c
                    break
        a1 = cusp.numerator()
        c1 = cusp.denominator()
        # Find matrix that maps infinity to cusp.
        gamma = complete_column(a1,c1)

    except TypeError:
        gamma = mat
        if gamma[1][0] == 0:
            cusp = Cusp(Infinity)
        else:
            cusp = Cusp(QQ(gamma[0][0])/QQ(gamma[1][0]))

    # Find the width w of this cusp; final answer should be a series in q_w
    width = group.cusp_width(cusp)

    if verbose:
        print('Matrix that maps Infinity to {}:'.format(mat), gamma)
        print('Width of cusp:', width)

    D = DirichletGroup(N)
    d = len(D)
    prim_chars = [phi.primitive_character().minimize_base_ring() for phi in D]

    if base_ring==None:
        Nbig = lcm(N, euler_phi(N))
        base_ring = CyclotomicField(Nbig)
    if base_ring==CC and cmplx_embedding==None:
        cmplx_embedding = 0

    if verbose:
        print('Calculations will be performed in the following field: {}'
               .format(base_ring))
        print('An index [k,i1,i1,t] stands for the Eisenstein series \
               E_k^(phi_i1,phi_i2,t), where phi_a is the a-th character \
               of DirichletGroup(N).')
        print('An index [l1, l2, i1, i2, t1, t2, t] stands for the product \
               E_l1^(phi_i1,phi_i2,t1*t)*E_l2^(phi_i1.bar(),phi_i2.bar(),t2*t).')
    Q = PowerSeriesRing(base_ring, 'q')
    q = Q.gen()


    if len(ind[0]) == 4:
        k = ind[0][0]
    elif len(ind[0]) == 7:
        k = ind[0][0] + ind[0][1]

    s = None
    if verbose:
        nonzero = len([0 for c in coeffs if c != 0])
        nonzero_counter = 1
    for i in range(len(coeffs)):
        if coeffs[i] == 0:
            continue
        if verbose:
            print('Adding series {} (out of {})'.format(nonzero_counter, nonzero))
            nonzero_counter += 1
        if len(ind[i]) == 4:
            if verbose:
                print('Eisenstein series of index {}'.format(ind[i]))
            k, i1, i2, t1 = ind[i]
            psi, phi = prim_chars[i1], prim_chars[i2]

            if not eis_alt:
                E = e_phipsi(psi,
                             phi,
                             k,
                             t=t1,
                             prec=prec,
                             mat=gamma, base_ring=base_ring)
            else:
                E = e_phipsi_alt(psi,
                             phi,
                             k,
                             t=t1,
                             prec=prec,
                             mat=gamma, base_ring=base_ring)
            E.pad(N)
            E.prune(width)
            if base_ring != CC:
                s = coeffs[i]*E if s == None else s + coeffs[i]*E
            else:
                s = coeffs[i].complex_embeddings()[cmplx_embedding]*E if s == None else s + coeffs[i].complex_embeddings()[cmplx_embedding]*E
        elif len(ind[i]) == 7:
            # ind[i] has the form [l, k-l, i, j, t1, t2, t]
            # corresponding to the product of Eisenstein series
            # E_l^{\phi,\psi}|B_{t_1t}*E_{k-l}^{\phi^{-1},\psi^{-1}}|B_{t_2t}
            l1, l2, i1, i2, t1, t2, t = ind[i]
            phi, psi = prim_chars[i1], prim_chars[i2]
            if verbose:
                print('Product of Eisenstein series of index', ind[i])
            if not eis_alt:
                E1 = e_phipsi(phi,
                              psi,
                              l1,
                              t = t1*t,
                              prec=prec,
                              mat=gamma, base_ring=base_ring)
                E2 = e_phipsi(phi**(-1),
                              psi**(-1),
                              l2,
                              t=t2*t,
                              prec=prec,
                              mat=gamma, base_ring=base_ring)
            else:
                E1 = e_phipsi_alt(phi,
                              psi,
                              l1,
                              t = t1*t,
                              prec=prec,
                              mat=gamma, base_ring=base_ring)
                E2 = e_phipsi_alt(phi**(-1),
                              psi**(-1),
                              l2,
                              t=t2*t,
                              prec=prec,
                              mat=gamma, base_ring=base_ring)
            E = E1*E2
            E.pad(N)
            E.prune(width)
            if base_ring != CC:
                s = coeffs[i]*E if s == None else s + coeffs[i]*E
            else:
                s = coeffs[i].complex_embeddings()[cmplx_embedding]*E if s == None else s + coeffs[i].complex_embeddings()[cmplx_embedding]*E
    if verbose:
        print('Done!')
    return s
