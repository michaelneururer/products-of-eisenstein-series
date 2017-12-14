from sage.arith.srange import srange
from sage.arith.all import lcm, divisors, euler_phi
from sage.modular.dirichlet import DirichletGroup
from sage.modular.modform.constructor import ModularForms
from sage.modular.dims import dimension_modular_forms
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.integer_ring import IntegerRing
from sage.rings.number_field.number_field import CyclotomicField
from sage.rings.complex_field import ComplexField, ComplexNumber
from sage.rings.big_oh import O
from sage.matrix.constructor import Matrix
from sage.functions.log import exp
from sage.modules.free_module_element import vector

ZZ = IntegerRing()

def eisenstein_series_at_inf(phi, psi, k, prec=10, t=1,base_ring=None):
    r"""
    Return Fourier expansion of Eistenstein series at a cusp.

    INPUT:

    - ``phi`` -- Dirichlet character.
    - ``psi`` -- Dirichlet character.
    - ``k`` -- integer, the weight of the Eistenstein series.
    - ``prec`` -- integer (default: 10).
    - ``t`` -- integer (default: 1).

    OUTPUT:

    The Fourier expansion of the Eisenstein series $E_k^{\phi,\psi, t}$ (as
    defined by [Diamond-Shurman]) at the specific cusp.

    EXAMPLES:
    sage: phi = DirichletGroup(3)[1]
    sage: psi = DirichletGroup(5)[1]
    sage: E = eisenstein_series_at_inf(phi, psi, 4)
    """
    N1, N2 = phi.level(), psi.level()
    N = N1*N2
    #The Fourier expansion of the Eisenstein series at infinity is in the field Q(zeta_Ncyc)
    Ncyc = lcm([euler_phi(N1), euler_phi(N2)])
    if base_ring==None:
        base_ring = CyclotomicField(Ncyc)
    Q = PowerSeriesRing(base_ring, 'q')
    q = Q.gen()
    s = O(q**prec)

    #Weight 2 with trivial characters is calculated separately
    if k==2 and phi.conductor()==1 and psi.conductor()==1:
        if t==1:
            raise TypeError('E_2 is not a modular form.')
        s = 1/24*(t-1)
        for m in srange(1,prec):
            for n in srange(1,prec/m):
                s += n * (q**(m*n)-t*q**(m*n*t))
        return s+O(q**prec)

    if psi.level()==1 and k==1:
        s -= phi.bernoulli(k)/ k
    elif phi.level()==1:
        s -= psi.bernoulli(k)/ k

    for m in srange(1, prec/t):
        for n in srange(1,prec/t/m+1):
            s += 2* base_ring(phi(m)) * base_ring(psi(n)) * n**(k-1) * q**(m*n*t)
    return s+O(q**prec)


def product_space(chi, k, weights = False, base_ring=None, verbose=False):
    r"""
    Computes all eisenstein series, and products of pairs of eisenstein series
    of lower weight, lying in the space of modular forms of weight $k$ and
    nebentypus $\chi$.
    INPUT:
     - chi - Dirichlet character, the nebentypus of the target space
     - k - an integer, the weight of the target space
    OUTPUT:
     - a matrix of coefficients of q-expansions, which are the products of
     Eisenstein series in M_k(chi).

    WARNING: It is only for principal chi that we know that the resulting
    space is the whole space of modular forms.
    """

    if weights == False:
        weights = srange(1, k/2 + 1)
    weight_dict = {}
    weight_dict[-1] = [w for w in weights if w%2] # Odd weights
    weight_dict[1] = [w for w in weights if not w%2] # Even weights

    try:
        N = chi.modulus()
    except AttributeError:
        if chi.parent() == ZZ:
            N = chi
            chi = DirichletGroup(N)[0]

    Id = DirichletGroup(1)[0]
    if chi(-1) != (-1)**k:
        raise ValueError('chi(-1)!=(-1)^k')
    sturm = ModularForms(N, k).sturm_bound()+1
    if N>1:
        target_dim = dimension_modular_forms(chi, k)
    else:
        target_dim = dimension_modular_forms(1, k)
    D = DirichletGroup(N)
    # product_space should ideally be called over number fields. Over complex
    # numbers the exact linear algebra solutions might not exist.
    if base_ring==None:
        base_ring = CyclotomicField(euler_phi(N))

    Q = PowerSeriesRing(base_ring, 'q')
    q = Q.gen()

    d = len(D)
    prim_chars = [phi.primitive_character() for phi in D]
    divs = divisors(N)

    products = Matrix(base_ring,[])
    indexlist = []
    rank = 0
    if verbose:
        print D
        print 'Sturm bound', sturm
        #TODO: target_dim needs refinment in the case of weight 2.
        print 'Target dimension', target_dim
    for i in srange(0, d): # First character
        phi = prim_chars[i]
        M1 = phi.conductor()
        for j in srange(0, d): # Second character
            psi = prim_chars[j]
            M2 = psi.conductor()
            if not M1*M2 in divs:
                continue
            parity = psi(-1) * phi(-1)
            for t1 in divs:
                if not M1*M2*t1 in divs:
                    continue
                #TODO: THE NEXT CONDITION NEEDS TO BE CORRECTED. THIS IS JUST A TEST
                if phi.bar() == psi and not (k==2): #and i==0 and j==0 and t1==1):
                    E = eisenstein_series_at_inf(phi, psi, k, sturm, t1,base_ring).padded_list()
                    try:
                        products.T.solve_right(vector(base_ring,E))
                    except ValueError:
                        products = Matrix(products.rows()+[E])
                        indexlist.append([k, i, j, t1])
                        rank+=1
                        if verbose:
                            print 'Added ', [k,i,j,t1]
                            print 'Rank is now', rank
                        if rank == target_dim:
                            return products,indexlist
                for t in divs:
                    if not M1*M2*t1*t in divs:
                        continue
                    for t2 in divs:
                        if not M1*M2*t1*t2*t in divs:
                            continue
                        for l in weight_dict[parity]:
                            if l == 1 and phi.is_odd():
                                continue
                            if i == 0 and j == 0 and (l == 2 or l == k-2):
                                continue
                            #TODO: THE NEXT CONDITION NEEDS TO BE REMOVED. THIS IS JUST A TEST
                            if l == 2 or l == k-2:
                                continue
                            E1 = eisenstein_series_at_inf(phi, psi, l, sturm, t1*t, base_ring)
                            E2 = eisenstein_series_at_inf(phi**(-1), psi**(-1), k-l, sturm, t2*t, base_ring)
                            #If chi is non-principal this needs to be changed to be something like chi*phi^(-1) instead of phi^(-1)
                            E = (E1 * E2 + O(q**sturm)).padded_list()
                            try:
                                products.T.solve_right(vector(base_ring,E))
                            except ValueError:
                                products = Matrix(products.rows()+[E])
                                indexlist.append([l, k-l, i, j, t1, t2, t])
                                rank+=1
                                if verbose:
                                    print 'Added ', [l, k-l, i, j, t1, t2, t]
                                    print 'Rank', rank
                                if rank == target_dim:
                                    return products, indexlist
    return products, indexlist
