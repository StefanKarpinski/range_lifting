function rand_ival(;
    max::Int64 = 1000,
    offset::Int64 = 0,
)
    b = rand(2:max)
    a = rand(1:b-1)
    d = rand(2:max)
    c = rand(1:d-1)
    lo, hi = a//b, c//d
    if hi < lo
        lo, hi = hi, lo
    end
    return offset + lo, offset + hi
end

function simplest_frac((x, y)::NTuple{2,Rational})
    @assert 0 < x ≤ y

    s, t = x.num, x.den
    u, v = y.num, y.den

    a = d = 1
    b = c = 0

    while true
        q = (s - 1) ÷ t
        s, t, u, v = v, u-q*v, t, s-q*t
        a, b, c, d = b+q*a, a, d+q*c, c
        s ≤ t && break
    end

    return (a + b)//(c + d)
end

function smallest_denominator(v::NTuple{2,Rational})
    simplest_frac(v).den
end

function smallest_denominator(vs::NTuple{2,Real}...)
    for (lo, hi) in vs
        @assert lo ≤ hi
    end
    d = 0
    while true
    @label next
        d += 1
        for (lo, hi) in vs
            ceil(d*lo) ≤ floor(d*hi) || @goto next
        end
        return d
    end
end

function cfrac(x::Real)
    A = Int64[]
    while true
        a, f = fldmod(x, 1)
        push!(A, a)
        iszero(f) && break
        x = inv(f)
    end
    return A
end

function child(A::Vector{T}, right::Bool) where {T<:Integer}
    A = copy(A)
    if iseven(length(A)) ⊻ right
        A[end] += 1
    else
        A[end] -= 1
        push!(A, T(2))
    end
    return A
end

child_l(A::Vector{<:Integer}) = child(A, false)
child_r(A::Vector{<:Integer}) = child(A, true)

child_l(r::Rational) = frac(child_l(cfrac(r)))
child_r(r::Rational) = frac(child_r(cfrac(r)))

function up(A::Vector{T}) where {T<:Integer}
    A = copy(A)
    A[end] -= 1
    if length(A) > 1 && A[end] == one(T)
        pop!(A)
        A[end] += 1
    end
    return A
end
up(x::Real) = frac(up(cfrac(x)))

function ancestor(pred::Function, A::Vector{T}) where {T<:Integer}
    x = frac(A)
    while true
        A = up(A)
        pred(A) && return A
    end
end

function ancestor_l(A::Vector{T}) where {T<:Integer}
    x = frac(A)
    ancestor(A->frac(A) < x, A)
end

ancestor_l(x::Real) = frac(ancestor_l(cfrac(x)))
ancestor_r(x::Real) = frac(ancestor_r(cfrac(x)))

function ancestor_r(A::Vector{T}) where {T<:Integer}
    x = frac(A)
    ancestor(A->frac(A) > x, A)
end

ancestor(A::Vector{T}, B::Vector{T}) where {T<:Integer} =
    (ancestors(A) ∩ ancestors(B))[1]

ancestor(v::Tuple{R,R}) where {R<:Real} =
    frac(ancestor(cfrac(v[1]), cfrac(v[2])))

function ancestors(pred::Function, A::Vector{T}) where {T<:Integer}
    As = [copy(A)]
    while A ≠ T[1]
        A = up(A)
        pred(A) && push!(As, A)
    end
    return As
end

ancestors(A::Vector{<:Integer}) = ancestors(Returns(true), A)

isancestor(A::Vector{T}, B::Vector{T}) where {T<:Integer} =
    A ∈ ancestors(B)
isancestor(x::Real, y::Real) = isancestor(cfrac(x), cfrac(y))

const ≼ = isancestor

function ancestors⁻(A::Vector{<:Integer})
    a = frac(A)
    ancestors(B -> frac(B) ≤ a, A)
end

function ancestors⁺(A::Vector{<:Integer})
    a = frac(A)
    ancestors(B -> frac(B) ≥ a, A)
end

ancestors(p::Function, x::Real) = map(frac, ancestors(p∘frac, cfrac(x)))
ancestors(x::Real) = map(frac, ancestors(cfrac(x)))
ancestors⁻(x::Real) = map(frac, ancestors⁻(cfrac(x)))
ancestors⁺(x::Real) = map(frac, ancestors⁺(cfrac(x)))

function partition((x, y)::NTuple{2,Real})
    @assert x ≤ y
    X = ancestors(z -> x ≤ z ≤ y, x)
    Y = ancestors(z -> x ≤ z ≤ y, y)
    @assert issorted(X, rev=false)
    @assert issorted(Y, rev=true)
    @assert X[end] == Y[end]
    P = X ∪ reverse(Y)
    @assert issorted(P)
    @assert all(cross_det(P[i], P[i+1]) == 1 for i=1:length(P)-1)
    return P
end

function frac(A::Vector{T}) where {T<:Integer}
    n, d = one(T), zero(T)
    for a in Iterators.reverse(A)
        n, d = d+a*n, n
    end
    return n//d
end

function cfrac_tree(r::Rational, depth::Integer=5)
    v = zeros(typeof(r), 2^depth-1)
    v[1] = r
    for i = 2:length(v)
        p = v[i >> 1]
        v[i] = iseven(i) ? child_l(p) : child_r(p)
    end
    return v
end

function print_btree(io::IO, v::Vector)
    n = length(v)
    d = ceil(Int, log2(n+1))
    w = maximum(textwidth∘string, v)
    for r = 2^(d-1):2^d-1
        for i = reverse(1:n)
            j = i << (leading_zeros(i)-8*sizeof(Int)+d)
            j == r || continue
            x = v[i]
            print(io, ' ', lpad(string(x), w))
        end
        println(io)
    end
end
print_btree(v::Vector) = print_btree(stdout, v)

gen_ivals() = while true
    v1 = rand_ival()
    v2 = rand_ival()

    # simplest fractions in each
    f1 = simplest_frac(v1); d1 = f1.den
    f2 = simplest_frac(v2); d2 = f2.den

    # smallest common denominator
    d = smallest_denominator(v1, v2)

    # skip easy cases
    max(d1, d2) < d || continue

    # find n1, n2 corresponding to common d
    n1 = ceil(Int, d*v1[1])
    n2 = ceil(Int, d*v2[1])

    # skip if numerator ratio is easy to find
    r = n1//n2 # optimal ratio
    isancestor(r, f1/f2) && continue

    # find upper bound on solutions
    r⁺ = f1/f2 # known solution
    # PROBLEM: known solution doesn't always appear as solution
    # according to the criterion below with d⁻ and d⁺
    while true
        # move up Stern-Brocot tree while feasible
        r′ = up(r⁺)
        d⁻ = max(ceil(Int, r′.num/v1[2]), ceil(Int, r′.den/v2[2]))
        d⁺ = min(floor(Int, r′.num/v1[1]), floor(Int, r′.den/v2[1]))
        d⁻ ≤ d⁺ || break
        r⁺ = r′
    end

    # continue if siblings with optimal ratio
    up(r) == up(r⁺) && continue

    return v1, v2

    vr = v1[1]/v2[2], v1[2]/v2[1]
    r⁻ = simplest_frac(vr)
    tr = cfrac_tree(r⁻)
end

# NON-WORKING ALGORITHM
function smallest_denominator′(x::Rational{Int}, y::Rational{Int})
    a, b = x.num, x.den
    c, d = y.num, y.den
    g, m, n = gcdx(b, d)
    M = b*d÷g
    u = mod(invmod(-a,b)*n*(d÷g), M)
    v = mod(invmod(c,d)*m*(b÷g), M)
    if u > v
        u -= M
    else
        v -= M
    end
    D, i, j = gcdx(u, v)
    @assert i ≥ 0 && j ≥ 0
    i %= b
    j %= d
    s = 1
    while (s*i % b)*d + (s*j % d)*b > (s*D)*(b*c - a*d)
        s += 1
    end
    D = s*D
    i = s*i % b
    j = s*j % d
end

mediant(x::Rational, y::Rational) = (x.num + y.num)//(x.den + y.den)

function mediant_tree(iv::NTuple{2,NTuple{2,Integer}}, d::Integer=5)
    v = [iv...]
    for _ = 1:d
        for i = reverse(1:length(v)-1)
            insert!(v, i+1, v[i] .+ v[i+1])
        end
    end
    return v
end

mediant_tree(iv::NTuple{2,Rational{<:Integer}}, d::Integer=5) =
    map(t -> Rational(t...), mediant_tree(map(r -> (r.num, r.den), iv), d))

cross_det(x::Rational, y::Rational) = x.den*y.num - x.num*y.den
cross_det(x::NTuple{2,Real}, y::NTuple{2,Real}) = x[2]*y[1] - x[1]*y[2]

#=
v = (x, y) = (1054//361, 2721//926)
v = (x, y) = rand_ival()

f = simplest_frac((x, y))
cross_det(x, y)
cross_det(x, f)
cross_det(f, y)
cross_det(x, mediant(x, f))
cross_det(mediant(x, f), f)

cross_det(f, mediant(f, y))
cross_det(mediant(f, y), y)

for _ = 1:1000
    x, y = rand_ival()
    1 in [cross_det(x, z) for z in ancestors(x)] &&
    1 in [cross_det(z, y) for z in ancestors(y)] && continue
    @show x, y
end
=#

function lcc(a::Int, b::Int, c::Int, d::Int)
    if a < b
        a, b = b, a
    end
    if c < d
        c, d = d, c
    end
    if a < c
        a, b, c, d = c, d, a, b
    end
    println((a, b, c, d))

    g_bd, u_bd = gcdx(b, d)
    g_cd, u_cd = gcdx(c, d)

    n = b*d÷g_bd # solution when i = k = 0

    for i = 0:fld(n-1,a)
        k = mod(a*i*u_cd, g_bd)
        if i == k == 0
            k += g_bd
        end
        c*k < n || continue
        p = a*i - c*k
        j = mod(-p*u_bd,d)÷g_bd
        l = (b*j + p)÷d
        @assert a*i + b*j == c*k + d*l
        @assert !any(a*i + b*j == c*k + d*l for j=0:j-1, l=0:l-1)
        n′ = a*i + b*j
        println((i, j, k, l) => n′)
        n = min(n, n′)
    end
    return n
end
