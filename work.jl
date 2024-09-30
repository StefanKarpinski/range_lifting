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

for _ = 1:500
    v1 = rand_ival(offset=2)
    v2 = rand_ival(offset=2)
    r1 = simplest_frac(v1); d1 = r1.den
    r2 = simplest_frac(v2); d2 = r2.den
    d = smallest_denominator(v1, v2)
    max(r1.den, r2.den) < d || continue
    n1 = ceil(d*v1[1]); @assert v1[1] ≤ n1//d ≤ v1[2]
    n2 = ceil(d*v2[1]); @assert v2[1] ≤ n2//d ≤ v2[2]
    vr = v1[1]/v2[2], v1[2]/v2[1]
    r⁻ = simplest_frac(vr)
    r = n1//n2
    r⁺ = r1/r2
    @show v1, v2
    @show d1, d2, d
    @show r⁻, r, r⁺, r ≼ r⁺, r⁺ ≼ r
end

# (26//105, 86//289), (61//404, 63//292): 4, 5, 11, 11
# v1.lo: 26//105 1//4 1//3 1//2 1//1
# v1.hi: 86//289 61//205 36//121 11//37 8//27 5//17 2//7 1//4
# v2.lo: 61//404 53//351 45//298 37//245 29//192 21//139 13//86 5//33 2//13 1//6 1//5 1//4 1//3 1//2 1//1
# v2.hi: 63//292 11//51 3//14 1//5

function tree(n::Integer)
    root = ((1,0,0), (0,1,0), (0,0,1))
    list = Vector{typeof(root)}(undef, n)
    list[1] = root
    for i = 2:n
        p = list[i >> 1]
        list[i] = iseven(i) ?
            (p[1], p[1].+p[2], p[2]) :
            (p[2], p[2].+p[3], p[3])
    end
    return list
end

L = [1 0 0; 1 1 0; 0 1 0]
R = [0 1 0; 0 1 1; 0 0 1]

function coprimes(n::Integer, a::Integer, b::Integer)
    root = (a, b)
    list = Vector{typeof(root)}(undef, n)
    list[1] = root
    for i = 2:n
        a, b = list[(i+1)÷3]
        list[i] =
            i % 3 == 2 ? (2a - b, a) :
            i % 3 == 0 ? (2a + b, a) :
            i % 3 == 1 ? (a + 2b, b) : error()
    end 
    return list
end
