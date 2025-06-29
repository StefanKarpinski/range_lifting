function rand_ival(;
    max::Int64 = 1000,
    offset::Int64 = 0,
)
    while true
        b = rand(2:max)
        a = rand(1:b-1)
        d = rand(2:max)
        c = rand(1:d-1)
        lo, hi = a//b, c//d
        lo == hi && continue
        if hi < lo
            lo, hi = hi, lo
        end
        lo += offset
        hi += offset
        # ensure there are some gaps in numerical semigroup
        if sum(ceil(k/hi) > floor(k/lo) for k = 1:20) ≥ 5
            return lo, hi
        end
    end
end

function simplest_frac(x::Rational, y::Rational)
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

function simplest_frac((x, y)::NTuple{2,Rational})
    simplest_frac(x, y)
end

function smallest_denominator(x::Rational, y::Rational)
    simplest_frac(x, y).den
end

function smallest_denominator((x, y)::NTuple{2,Rational})
    smallest_denominator(x, y)
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

smallest_numerator(x::Real, y::Real) =
    smallest_denominator(inv(y), inv(x))

smallest_numerator(vs::NTuple{2,Real}...) =
    smallest_denominator(map(v->map(inv, reverse(v)), vs)...)

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

function partition(x::Real, y::Real)
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

function partition((x, y)::NTuple{2,Real})
    partition(x, y)
end

function gaps(x::Real, y::Real)
    P = partition(x, y)
    g, i = findmin(1:length(P)-1) do i
        a1 = numerator(P[i])
        a2 = numerator(P[i+1])
        a1*a2 - a1 - a2
    end
    a1 = numerator(P[i])
    a2 = numerator(P[i+1])
    G = Int[]
    for j = 1:a2-1
        for k = 1:a1-1
            g = a1*a2 - j*a1 - k*a2
            g < 0 && break
            ceil(g/y) ≤ floor(g/x) && continue
            push!(G, g)
        end
    end
    return sort!(G)
end

function gaps((x, y)::NTuple{2,Real})
    gaps(x, y)
end

function expand_ival(x::Real, y::Real)
    if cross_det(x, y) == 1
        a1, b1 = numerator(x), denominator(x)
        a2, b2 = numerator(y), denominator(y)
        g = a1*a2 - a1 - a2
        x′ = (a1*g)//(b1*g + 1)
        y′ = (a2*g)//(b2*g - 1)
        return x′, y′
    else
        x′, y′ = 0//1, 1//0
        for g in gaps(x, y)
            x′ = max(x′, g/ceil(g/x))
            y′ = min(y′, g/floor(g/y))
        end
        return x′, y′
    end
end

function expand_ival((x, y)::NTuple{2,Real})
    expand_ival(x, y)
end

function commonize_ivals(vs::NTuple{2,Real}...)
    n = 2 # can insert a minimum value here
    for (x, y) in vs
        x′, y′ = expand_ival(x, y)
        # NOTE: simplified expr for x*x′/(x-x′) would help efficiency
        n = max(n, @show ceil(Int, 2x*x′/(x-x′)))
        n = max(n, @show ceil(Int, y*y′/(y′-y))-1)
    end
    n = nextpow(2, n)
    ds = map(vs) do (x, y)
        d_x = cld(n, x) | 1
        d_y = fld(n+1, y)
        x′, y′ = expand_ival(x, y)
        @assert x′ < n//d_x ≤ x < y ≤ (n+1)//d_y < y′
        d = (n+1)*d_x - n*d_y
        @assert isodd(d)
        # S([x, y]) == <n, n+1>/d (numerical semigroups)
        return d
    end
    return n, ds...
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

    n1 = smallest_numerator(v1)
    n2 = smallest_numerator(v2)
    n  = smallest_numerator(v1, v2)

    max(n1, n2) < n < lcm(n1, n2) || continue

    @show n1, n2, n

    a1, b1, c1 = ival_abc(v1...)
    a2, b2, c2 = ival_abc(v2...)

    g, u, v = gcdx(b1, b2)
    b1′ = b1 ÷ g
    b2′ = b2 ÷ g
    l = b1*b2′ # lcm(b1, b2)

    d1(n) = c1*n - mod(a1*n, b1)
    d2(n) = c2*n - mod(a2*n, b2)

    any(0:g-1) do n_g
        n(i1,i2) = n_g + i1*b2 + i2*b1
        d1(n(1,0)) < 0 || d1(n(0,1)) < 0 ||
        d2(n(1,0)) < 0 || d2(n(0,1)) < 0
    end || continue

    return v1, v2
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

function dgcdx(a::Int, b::Int)
    g, u, v = gcdx(a, b)
    @assert g == u*a + v*b
    v = -v
    @assert g == u*a - v*b
    if u < 0 || v < 0
        u += b ÷ g
        v += a ÷ g
    end
    @assert u ≥ 0 && v ≥ 0
    @assert g == u*a - v*b
    return g, u, v
end

function lclc_brute(a::Int, b::Int, c::Int, d::Int)
    g = gcd(b, d)
    n = b*d÷g # lcm(b, d)
    t = (0, d÷g, 0, b÷g)
    i = 0
    while a*i < n
        j = i == 0 ? 1 : 0
        while (n′ = a*i + b*j) < n
            k = 0
            while k*c ≤ n′
                l, r = divrem(n′ - k*c, d)
                if r == 0
                    t = (i, j, k, l)
                    n = n′
                    break
                end
                k += 1
            end
            j += 1
        end
        i += 1
    end
    return n => t
end

# compute: m(<a1, b1>/c1 ∩ <a2, b2>/c2)
function lclc_brute(
    a1::Int, b1::Int, c1::Int,
    a2::Int, b2::Int, c2::Int,
)
    n = lcm(b1, b2)
    i1 = 0
    while a1*i1 < c1*n
        j1 = i1 == 0 ? 1 : 0
        while a1*i1 + b1*j1 < c1*n
            n′, r = divrem(a1*i1 + b1*j1, c1)
            if n′ < n && r == 0
                i2 = 0
                while a2*i2 ≤ c2*n′
                    j2, r = divrem(c2*n′ - a2*i2, b2)
                    if r == 0
                        n = n′
                        break
                    end
                    i2 += 1
                end
            end
            j1 += 1
        end
        i1 += 1
    end
    return n
end

#=
for _ = 1:10000
    a1, b1, a2, b2 = rand(1:50, 4)
    gcd(a1, b1) == 1 || continue
    gcd(a2, b2) == 1 || continue
    # gcd(a1, a2) > 1  || continue
    # gcd(a1, b2) > 1  || continue
    # gcd(b1, a2) > 1  || continue
    # gcd(b1, b2) > 1  || continue
    @show a1, b1, a2, b2
    n, (i1, j1, i2, j2) = lclc_brute(a1, b1, a2, b2)
    @assert n == a1*i1 + b1*j1 == a2*i2 + b2*j2
    g, u, v = gcdx(b1, b2)
    b1′ = b1 ÷ g
    b2′ = b2 ÷ g
    l = b1*b2′ # lcm(b1, b2)
    @assert mod(i2 - i1*a1*invmod(a2, g), g) == 0
    @assert mod1(a1*i1*v*b2′ + a2*i2*u*b1′, l) == n
    i2′ = mod(i1*a1*invmod(a2, g), g)
    @assert mod1(a1*i1*v*b2′ + a2*i2′*u*b1′, l) == n
end
=#

function ival_abc(x::Rational, y::Rational)
    x.den*y.num,
    x.num*y.num,
    x.den*y.num - x.num*y.den
end

# least common linear combination, i.e. smallest positive n such that
#
#   n == a1*i1 + b1*j1 == a2*i2 + b2*j2
#
# for nonnegative i1, j1, i2, j2
#
function lclc(
    a1::Int, b1::Int, c1::Int,
    a2::Int, b2::Int, c2::Int,
)
    b1, a1 = minmax(b1, a1)
    b2, a2 = minmax(b2, a2)
    if a1*c2 < a2*c1 # a1/c1 < a2/c2
        a1, a2 = a2, a1
        b1, b2 = b2, b1
        c1, c2 = c2, c1
    end

    # inverses we need
    c1⁻¹ = invmod(c1, b1)
    c2⁻¹ = invmod(c2, b2)
    a2⁻¹ = invmod(a2, b2)

    # gcd & lcm of b1, b2
    g, u, v = gcdx(b1, b2)
    b1′ = b1 ÷ g
    b2′ = b2 ÷ g
    l = b1*b2′ # lcm(b1, b2)

    n = l # solution when i1 = i2 = 0
    i1 = 0
    while i1*a1 < n*c1
        i2 = mod(i1*a1*c1⁻¹*a2⁻¹*c2, g)
        i1 == i2 == 0 && (i2 += g)
        while i2*a2 < n*c2
            n′ = mod(i1*a1*c1⁻¹*v*b2′ + i2*a2*c2⁻¹*u*b1′, l)
            if n′ < n && n′*c1 ≥ i1*a1 && n′*c2 ≥ i2*a2
                n = n′
            end
            i2 += g
        end
        i1 += 1
    end

    return n
end

function rand_coprime(n::Int; min::Int=1, max::Int=100)
    while true
        t = ntuple(i -> rand(min:max), n)
        all(gcd(t[i],t[j]) == 1 for i=1:n-1 for j=i+1:n) && return t
    end
end

function coeffs(n::Int, a::Int, b::Int)
    for i = 0:n÷a, j = 0:(n-a*i)÷b
        a*i + b*j == n && return (i, j)
    end
    nothing
end

#=
for _ = 1:1000
    a1, b1 = rand_coprime(2)
    a2, b2 = rand_coprime(2)
    n = lclc(a1, b1, a2, b2)
    @assert !isnothing(coeffs(n, a1, b1))
    @assert !isnothing(coeffs(n, a2, b2))
    for n′ = 1:n-1
        @assert isnothing(coeffs(n′, a1, b1)) ||
                isnothing(coeffs(n′, a2, b2))

    end
end
=#

#=
for _ = 1:1000
    a1, b1, c1 = rand_coprime(3)
    a2, b2, c2 = rand_coprime(3)
    @show a1, b1, c1, a2, b2, c2
    n = lclc(a1, b1, c1, a2, b2, c2)
    @assert !isnothing(coeffs(c1*n, a1, b1))
    @assert !isnothing(coeffs(c2*n, a2, b2))
    for n′ = 1:n-1
        @assert isnothing(coeffs(c1*n′, a1, b1)) ||
                isnothing(coeffs(c2*n′, a2, b2))
    end
end
=#
