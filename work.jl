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

function smallest_denominator(vs::NTuple{2,Real}...)
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

function simplest_frac(v::NTuple{2,Real})
    d = smallest_denominator(v)
    n = ceil(d*v[1])
    return n//d
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
ancestors(x::Real) = map(frac, ancestors(cfrac(x)))

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
            print(io, ' ', rpad(string(x), w))
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
