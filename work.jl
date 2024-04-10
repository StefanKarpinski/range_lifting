using Base: TwicePrecision

function tz(x::AbstractFloat)
    n, p = Base.decompose(x)
    trailing_zeros(n) + p
end

tz(n::Integer) = trailing_zeros(n)
tz(x::TwicePrecision) = iszero(x.lo) ? tz(x.hi) : tz(x.lo)

# pick value in interval with the most trailing zeros
function simplest_float(lo::T, hi::T) where {T<:AbstractFloat}
    lo == hi && return lo
    hi < 0 && return -simplest_float(-hi, -lo)
    lo ≤ 0 && return zero(T)
    @assert 0 < lo < hi
    e = exponent(hi - lo)
    b = floor(ldexp(hi, -e))
    a = max(lo, ldexp(b - 1, e))
    b = ldexp(b, e)
    m = tz(a) ≥ tz(b) ? a : b
    @assert lo ≤ m ≤ hi
    return m
end

function simplest_rational_core(
    (s, t)::Tuple{T,T},
    (u, v)::Tuple{T,T},
) where {T<:Real}
    𝟘 = zero(T)
    𝟙 = one(T)

    a = d = 𝟙
    b = c = 𝟘

    while true
        q = s ÷ t
        s, t, u, v = v, u-q*v, t, s-q*t
        a, b, c, d = b+q*a, a, d+q*c, c
        s < t && break
    end

    return a + b, c + d
end

function simplest_rational(
    (s, t)::Tuple{T,T},
    (u, v)::Tuple{T,T},
) where {T<:Real}
    n, d = simplest_rational_core((s, t), (u, v))
    # lower bound for n
    n⁻ = prevfloat(cld(d*s, t))
    while n⁻ < n && n⁻*t < d*s # n⁻/d < s/t
        n⁻ = nextfloat(n⁻)
    end
    # upper bound for n
    n⁺ = nextfloat(fld(d*u, v))
    while n < n⁺ && n⁺*v > d*u # u/v < n⁺/d
        n⁺ = prevfloat(n⁺)
    end
    # simplify n
    n = simplest_float(n⁻, n⁺)
    return n, d
end

function canonicalize(large::T, small::T) where {T<:AbstractFloat}
    h = large + small
    h, (large - h) + small
end

function g_ival(a::T, c::T) where {T<:AbstractFloat}
    h = a/c
    δ = fma(-c, h, a) # δ == a - c*h
    # lower bound
    a⁻ = prevfloat(a)
    l⁻ = nextfloat(0.5*(δ + fma(-c, h, a⁻))/c)
    h⁻, l⁻ = canonicalize(h, l⁻)
    while fma(c, h⁻, c*l⁻) > a⁻
        l⁻ = prevfloat(l⁻)
    end
    l⁻ = nextfloat(l⁻)
    h⁻, l⁻ = canonicalize(h⁻, l⁻)
    @assert fma(c, h⁻, c*l⁻) == a
    @assert fma(c, h⁻, c*prevfloat(l⁻)) == a⁻
    # upper bound
    a⁺ = nextfloat(a)
    l⁺ = prevfloat(0.5*(δ + fma(-c, h, a⁺))/c)
    h⁺, l⁺ = canonicalize(h, l⁺)
    while fma(c, h⁺, c*l⁺) < a⁺
        l⁺ = nextfloat(l⁺)
    end
    l⁺ = prevfloat(l⁺)
    h⁺, l⁺ = canonicalize(h⁺, l⁺)
    @assert fma(c, h⁺, c*l⁺) == a
    @assert fma(c, h⁺, c*nextfloat(l⁺)) == a⁺
    # return interval
    (h⁻, l⁻), (h⁺, l⁺)
end

function min_hi_lo(x::Tuple{T,T}, y::Tuple{T,T}) where {T<:AbstractFloat}
    x[1] < y[1] ? x :
    y[1] < x[1] ? y :
    x[2] < y[2] ? x : y
end

function max_hi_lo(x::Tuple{T,T}, y::Tuple{T,T}) where {T<:AbstractFloat}
    x[1] > y[1] ? x :
    y[1] > x[1] ? y :
    x[2] > y[2] ? x : y
end

function div_hi_lo(x::T, y::T) where {T<:AbstractFloat}
    xs, xe = frexp(x)
    ys, ye = frexp(y)
    r = xs / ys
    rh, rl = canonicalize(r, -fma(r, ys, -xs)/ys)
    ldexp(rh, xe-ye), ldexp(rl, xe-ye)
end

struct FRange{T<:AbstractFloat} <: AbstractRange{T}
    c::T
    d::T
    n::T
    h::T
    l::T
end

Base.length(r::FRange) = Int(r.n) + 1
Base.step(r::FRange) = fma(r.d, r.h, r.d*r.l)

function Base.getindex(r::FRange, i::Int)
    k = fma(i-1, r.d, r.c)
    x = fma(k, r.h, k*r.l)
end

# example: (a, s, b) = (-3e50, 1e50, 4e50)
# example: (a, s, b) = (-1e20, 3.0, 2e20)
# problem: can be made to hit zero but shouldn't!
# worse: (a, s, b) = (-1.0e17, 0.3, 2.0e18)
# another: (a, s, b) = (-1e14, .9, 8e15)

function range_ratios(a::T, s::T, b::T) where {T<:AbstractFloat}
    a⁻, a⁺ = prevfloat(a), nextfloat(a)
    b⁻, b⁺ = prevfloat(b), nextfloat(b)
    s⁻, s⁺ = prevfloat(s), nextfloat(s)
    if signbit(s)
        s⁻, s⁺ = s⁺, s⁻
    end
    n⁻ = cld(b⁻ - a⁺, s⁺)
    n⁺ = fld(b⁺ - a⁻, s⁻)
    @assert n⁻ ≤ n⁺ # otherwise can't hit endpoint
    n = simplest_float(n⁻, n⁺)
    p = tz(n)
    # make everything non-negative
    if signbit(a)
        a⁻, a⁺ = -a⁺, -a⁻
    end
    if signbit(s)
        s⁻, s⁺ = -s⁻, -s⁺
    end
    if signbit(b)
        b⁻, b⁺ = -b⁺, -b⁻
    end
    # find best grid divisor
    c = d = e = zero(T)
    while true
        d += one(T)
        # find simplest c
        c⁻ = cld(d*a⁻, s⁺)
        c⁺ = fld(d*a⁺, s⁻)
        c⁻ ≤ c⁺ || continue
        c = simplest_float(c⁻, c⁺)
        tz(c) ≥ p || continue
        # find simplest e
        e⁻ = cld(d*b⁻, s⁺)
        e⁺ = fld(d*b⁺, s⁻)
        e⁻ ≤ e⁺ || continue
        e = simplest_float(e⁻, e⁺)
        tz(e) ≥ p || continue
        # found good c & e
        break
    end
    # eliminated common powers of two
    z = min(tz(c), tz(d), tz(e))
    c = ldexp(c, -z)
    d = ldexp(d, -z)
    e = ldexp(e, -z)
    # restore signs for endpoints
    signbit(a) && (c = -c)
    signbit(b) && (e = -e)
    # return values
    n, c, d, e
end

function lift_range(a::T, s::T, b::T) where {T<:AbstractFloat}
    # find the relative grid ratios
    n, c, d, e = range_ratios(a, s, b)
    # integers such that:
    #  - c = d*a/s
    #  - e = d*b/s
    # still need rational value g:
    #  - g = s/d = a/c = b/e
    # get double precision bounds on g:
    g_a⁻, g_a⁺ = g_ival(abs(a), abs(c))
    g_b⁻, g_b⁺ = g_ival(abs(b), abs(e))
    g⁻ = max_hi_lo(g_a⁻, g_b⁻)
    g⁺ = min_hi_lo(g_a⁺, g_b⁺)
    h, l = canonicalize(
        0.5*(g⁻[1] + g⁺[1]),
        0.5*(g⁻[2] + g⁺[2]),
    )
    # check that this hits end-points and approximates step
    @assert a == fma(c, h, c*l)
    @assert s ≈  fma(d, h, d*l)
    @assert b == fma(e, h, e*l)
    # return range object
    FRange(c, d, n, h, l)
end
