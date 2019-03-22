using Simplicial
using Combinatorics

################################################################################
#          translating between oriented matroids and neural codes              #
################################################################################

"""
    codewordToTope(codeword, n)

Returns a vector 'tope' of length 'n', where 'tope[i] = 1' if 'i'
in sigma, 'tope[i] = -1' otherwise. 'sigma' should be a subset of [n]
"""
function codewordToTope(sigma, n)
    return [(-1)^(!(i in sigma)) for i=1:n]
end

"""
    codeToTopes(code)

Returns a list of topes, each tope translates a codeword of code.
Input should be a CombinatorialCode object.
"""
function codeToTopes(code)
    n = length(code.vertices)
    return [codewordToTope(codeword, n) for codeword in code]
end

"""
    function topeToCodeword(tope)

Input should be a vector tope with entries +, 0, -
Returns a codeword whose elements are the indices i where tope[i] = +1
"""
function topeToCodeword(tope)
    codeword = []
    for i = 1:length(tope)
        if tope[i] == 1
            push!(codeword, i)
        end
    end
    return codeword
end


"""
    function topesToCode(topes)

Input should be a list of vectors with entries +, 0, -
Returns a CombinatorialCode whose codewords come from vectors in our list
"""
function topesToCode(topes)
    codewords = [topeToCodeword(tope) for tope in topes]
    return CombinatorialCode(codewords)
end

"""
    function strToSignVec(str)

converts string str to a sign vector
"""
function strToSignVec(str)
    n = length(str)
    vec = zeros(n)
    for i=1:n
        if str[i] == '+'
            vec[i] = +1
        elseif str[i] == '-'
            vec[i] = -1
        end
    end
    return vec
end

################################################################################
#                      manipulating oriented matroids                          #
################################################################################

"""
    function composition(X, Y)

Returns the composition Z = X•Y of sign vectors X and Y. This is defined by
    Z(e) = X(e) if X(e) = + or -
    Z(e) = Y(e) if X(e) = 0
"""
function composition(X, Y)
    n = length(X)
    Z = deepcopy(X)
    for i=1:n
        if X[i] == 0
            Z[i] = Y[i]
        end
    end
    return Z
end

"""
    function S(X,Y)

Returns the disagreement set of sign vectors X and Y. This is the set of indices
where X(i) = + and Y(i) = - or  X(i) = - and Y(i) = +
"""
function S(X, Y)
    return [i for i in 1:length(X) if (X[i] == -Y[i]) && X[i] != 0]
end


"""
    function affineToCentral(topes)

Given topes of an affine oriented matroid, as a list of sign vectors, returns
list of topes of the centralized oriented matroid.

Plane "at infinity" is added at the end of each tope.
"""
function affineToCentral(topes)
    result = []
    start = deepcopy(topes)
    for T in start
        push!(T, +1)
        push!(result, T)
        push!(result, -T)
    end
    return result
end

################################################################################
#                   checking whether things are matroids                       #
################################################################################

"""
    function checkUniformTopeAxioms(topes)

Given a set of potential topes of a uniform OM, presented as a vector of +/- 1
int64 arrays.

Uses Lawrences's axioms for uniform oriented matroids
(Excercise 3.28 in red book, Lawrence 1983)
"""

function checkUniformTopeAxioms(topes)
    all_restrictions = allRestrictions(topes)
    #check T0: topes \neq \emptyset
    if length(topes) == 0
        return false
    end
    #check T1: topes = -topes
    for T in topes
        if !(-T in topes)
            return false
        end
    end
    #check TU2: if X\subset {0, +, -}^n is a restriction of some T in topes, then either there is some T in topes such that X\circ T \in topes, X\circ -T \notin topes, or X\circ Y \in topes for all Y\in {0, +, -}^n
    for X in all_restrictions
        split = false #true if there is some T in topes such that X\circ T \in topes
        all = true #true if  X\circ T \in topes for all T\in topes
        for T in topes
            X1 = composition(X, T)
            X2 = composition(X, -T)
            if (X1 in topes) == !(X2 in topes)
                split = true
                all = false
            elseif (X1 in topes) == (X2 in topes) == false
                all = false
            end
        end
        if (split == false) && (all == true)
            for composition in allCompositions(X)
                if !(composition in topes)
                    all = false
                end
            end
        end
        if split == false && all == false
            return false
        end
    end
    return true
end

"""
    function checkTopeAxioms(topes)

given a set of potential topes, presented as a vector of +/- 1 int64 arrays,
returns true if topes is the set of topes of an oriented matroid and false otherwise.

uses Da Silva's axioms
(Excercise 3.31 in red book)
"""

function checkTopeAxioms(topes)
    all_restrictions = allRestrictions(topes)
    #check T0: topes \neq \emptyset
    if length(topes) == 0
        return false
    end
    #check T1: topes = -topes
    for T in topes
        if !(-T in topes)
            return false
        end
    end
    #check T2: if X\subset {0, +, -}^n is a restriction of some T in topes, then either there is some T in topes such that X\circ T \in topes, X\circ -T \notin topes, or X\circ T \in topes for all T\in topes
    for X in all_restrictions
        split = false #true if there is some T in topes such that X\circ T \in topes
        all = true #true if  X\circ T \in topes for all T\in topes
        for T in topes
            X1 = composition(X, T)
            X2 = composition(X, -T)
            if (X1 in topes) == !(X2 in topes)
                split = true
                all = false
            elseif (X1 in topes) == (X2 in topes) == false
                all = false
            end
        end
        if split == all == false
            return false
        end
    end
    return true
end


"""
    function findBadRestrictions(topes)

given a set of potential topes, presented as a vector of +/- 1 int64 arrays,
finds the set of sign vectors where Da Silva's axioms fail, ie X is a restriction
of some T in topes, but there is not a T in topes with X•T in topes, X•(-T) not
in topes, and X•T is not in topes for all T in topes

Nothing else depends on this function--I think it might be useful for some matroid
completion ideas, but haven't used it yet.
"""
function findBadRestrictions(topes)
    all_restrictions = allRestrictions(topes)
    bad_restrictions = []
    overall = true
    #check T0: topes \neq \emptyset
    if length(topes) == 0
        return (false,bad_restrictions)
    end
    #check T1: topes = -topes
    for T in topes
        if !(-T in topes)
            return (false, bad_restrictions)
        end
    end
    #check T2: if X\subset {0, +, -}^n is a restriction of some T in topes, then either there is some T in topes such that X\circ T \in topes, X\circ -T \notin topes, or X\circ T \in topes for all T\in topes
    for X in all_restrictions
        split = false #true if there is some T in topes such that X\circ T \in topes
        all = true #true if  X\circ T \in topes for all T\in topes
        for T in topes
            X1 = composition(X, T)
            X2 = composition(X, -T)
            if (X1 in topes) == !(X2 in topes)
                split = true
                all = false
            elseif (X1 in topes) == (X2 in topes) == false
                all = false
            end
        end
        if split == all == false
            overall = false
            push!(bad_restrictions, X)
        end
    end
    return (overall, bad_restrictions)
end

########### Checking whether things are matroids: helper functions #############

"""
    function restrictions(vector)

It takes a vector, and for each nonempty subset of the indices,
knocks out the nonzero entries to zero
it returns a list with these entires
"""


function restrictions(vector)
    n = length(vector)
    indices = collect(1:n).'
    result = []
    for subset in powerset(indices,0, n-1)
        restricted_vector = copy(vector)
        for index in subset
            restricted_vector[index] = 0
        end
        push!(result, restricted_vector)
    end
    return result
end


"""
    function allRestrictions(topes)

Given a list of sign vectors (topes), returns all unique sign vectors which
appear as restricitons of sign vectors in our list
"""

function allRestrictions(topes)
    result = []
    for T in topes
        for X in restrictions(T)
            if !(X in result)
                push!(result, X)
            end
        end
    end
    return result
end

"""
    function allCompositions(vector)

given a sign vector V in {0,+,-}^E, presented as a vector with entries
+1, -1, 0, computes V•X for X in {0,+,-}^E
returns this in a list
"""
function allCompositions(V)
    all_compositions = []
    free_spots = [i for i in 1:length(V) if V[i] == 0]
    subsets = powerset(free_spots)
    for subset in subsets
        vec = copy(V)
        for i in free_spots
            if i in subset
                vec[i] = +1
            else
                vec[i] = -1
            end
        end
        push!(all_compositions, vec)
    end
    return all_compositions
    return free_spots
end


################################################################################
#                  translating between chirotopes and topes                    #
################################################################################

"""
    function chirotopeToTopes(X, r, E)

Given chirotope X of rank r on ground set E

Returns topes of the corresponding oriented matroid.

See exercise 3.24 of red book for details on method.
"""
function chirotopeToTopes(X, r, E)
    Topes = []
    n = length(E)
    for i in 1:length(X)
        if X[i] != 0
            B = getBasis(i, n, r)
            for alpha in allSignVectors(r)
                T = TBalpha(B, alpha, X, E)
                if !(T in Topes)
                    push!(Topes, T)
                end
            end
        end
    end
    return Topes
end


########### Converting from chirotopes to topes: helper functions #############

"""
    function getIndex(circuit, n, k, order = "RevLex")

Input--unoriented basis as list of indices, n = |E|, k = rank.
Output--the index of this basis in "RevLex order," or at least in what this site
(http://www.om.math.ethz.ch/?p=catom) say is RevLex order.

"""
function getIndex(circuit, n, k, order = "RevLex")
    index = 1
    circ_copy = deepcopy(circuit)
    if !(issorted(circ_copy))
        sort!(circ_copy)
    end
    for i in 1:k
        offset = 0
        max_element = pop!(circ_copy)
        offset = binomial(max_element-1,k-i+1)
        index = index + offset
        n = n-1
    end
    return index
end

"""
    function basicCocircuit(b, B, E, X)

b element
E ground set
B basis
X chirotope

If B is a basis, b in B, then c*(b, B) is the unique signed cocircuit of M
which is positive on b and disjoint from B minus b.

This function returns c*(b, B) given b, B, E, and the chirotope X

For more see the beginning of 3.4 in the red book, page 115.
"""

function basicCocircuit(b, B, E, X)
    r = length(B)
    n = length(E)
    B_minus_b = filter(x-> !(x in values(b)), B)
    E_minus_B = filter(x-> !(x in B_minus_b), E)
    c = zeros(n)
    for element in E_minus_B
        basis = deepcopy(B_minus_b)
        unshift!(basis, element)
        sign = getSign(basis, X, n, r)
        c[element] = sign
    end
    if c[b] == -1
        c = -c
    end
    return c
end

"""
    function getSign(B, X, n, k)

Given B subset 1...n, |B| = k, X a chirotope of rank k in RevLex order
Return the sign of B in X
"""
function getSign(B, X, n, k)
    BB = deepcopy(B)
    b = BB[1]
    sorted_place = pop!(find(x -> x <= b, BB))
    parity = (sorted_place-1)%2
    index = getIndex(BB, n, k)
    sign = ((-1)^parity)*X[index]
    return sign
end

"""
    function TBalpha(B, alpha, X, E)

given a basis B, sign vector alpha, chirotope X, ground set E
returns tope T_{B, alpha} = alpha_1c*(b_1, B)•...•alpha_rc*(b_r, B)

See exercise 3.24 in the red book for details.
"""

function TBalpha(B, alpha, X, E)
    n = length(E)
    r = length(B)
    T = zeros(n)
    for i in 1:r
        b = B[i]
        a = alpha[i]
        c_b = basicCocircuit(b, B, E, X)
        T = composition(T, a*c_b)
    end
    return T
end


"""
    function getBasis(i, n, r)

Given index i, size of ground set n, rank r

Give the subset of 1...n of size r indexed by i in RevLex order.
"""
function getBasis(i, n, r)
    result = []
    while (i > 0) & (n> 0) & (r>0)
        if i <= binomial(n-1, r)
            n = n-1
        else
            push!(result, n)
            i = i- binomial(n-1, r)
            n = n-1
            r = r-1
        end
    end
    return reverse(result)
end

"""
    function allSignVectors

Returns in a list all vectors with entries +1, -1 of length r
"""
function allSignVectors(r)
    subsets = powerset([i for i=1:r])
    result = []
    for subset in subsets
        sign_vec = ones(r)
        for i in subset
            sign_vec[i] = -1
        end
        push!(result, sign_vec)
    end
    return result
end
