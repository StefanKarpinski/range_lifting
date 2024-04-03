function tz(x::AbstractFloat)
    n, p = Base.decompose(x)
    trailing_zeros(n) + p
end

tz(n::Integer) = trailing_zeros(n)

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

function ratio_p(x::AbstractFloat)
    n, p, s = Base.decompose(x)
    z = trailing_zeros(n)
    n >>>= z
    p += z
    s*n, p
end

function ratio(x::AbstractFloat)
    n, p = ratio_p(x)
    n, exp2(p)
end

function ratio(x::T, y::T) where {T<:AbstractFloat}
    x_n, x_p = ratio_p(x)
    y_n, y_p = ratio_p(y)
    p = x_p - y_p
    n = T(x_n)
    d = T(y_n)
    if p > 0
        n *= exp2(p)
    elseif p < 0
        d *= exp2(-p)
    end
    return flipsign(n, d), abs(d)
end

function ratio_ival(x::T, y::T) where {T<:AbstractFloat}
    neg = (x < 0) ⊻ (y < 0)
    x = abs(x); y = abs(y)
    lo_n, lo_d = ratio(prevfloat(x), nextfloat(y))
    hi_n, hi_d = ratio(nextfloat(x), prevfloat(y))
    if neg
        hi_n, lo_n = -lo_n, -hi_n
        hi_d, lo_d =  lo_d,  hi_d
    end
    return (lo_n, lo_d), (hi_n, hi_d)
end

function frac_part(
    (lo_n, lo_d)::Tuple{T,T},
    (hi_n, hi_d)::Tuple{T,T},
) where {T<:AbstractFloat}
    lo_q, lo_n = fldmod(lo_n, lo_d)
    hi_n -= lo_q*hi_d
    return (lo_n, lo_d), (hi_n, hi_d)
end

function ratio_max(
    (x_n, x_d)::Tuple{T,T},
    (y_n, y_d)::Tuple{T,T},
) where {T<:AbstractFloat}
    x_n*y_d ≥ y_n*x_d ? (x_n, x_d) : (y_n, y_d)
end

function ratio_min(
    (x_n, x_d)::Tuple{T,T},
    (y_n, y_d)::Tuple{T,T},
) where {T<:AbstractFloat}
    x_n*y_d ≤ y_n*x_d ? (x_n, x_d) : (y_n, y_d)
end

function ratio_max(
    x::Tuple{T,T},
    y::Tuple{T,T},
    z::Tuple{T,T},
) where {T<:AbstractFloat}
    ratio_max(ratio_max(x, y), z)
end

function ratio_min(
    x::Tuple{T,T},
    y::Tuple{T,T},
    z::Tuple{T,T},
) where {T<:AbstractFloat}
    ratio_min(ratio_min(x, y), z)
end

function canonicalize(large::T, small::T) where {T<:AbstractFloat}
    h = large + small
    h, (large - h) + small
end

function div_hi_lo(x::T, y::T) where {T<:AbstractFloat}
    xs, xe = frexp(x)
    ys, ye = frexp(y)
    r = xs / ys
    rh, rl = canonicalize(r, -fma(r, ys, -xs)/ys)
    ldexp(rh, xe-ye), ldexp(rl, xe-ye)
end

# example: (a, s, b) = (-3e50, 1e50, 4e50)
# example: (a, s, b) = (-1e20, 3.0, 2e20)
# problem: can be made to hit zero but shouldn't!
# worse: (a, s, b) = (-1.0e17, 0.3, 2.0e18)
# another: (a, s, b) = (-1e14, .9, 8e15)

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

function lift_range(a::T, s::T, b::T) where {T<:AbstractFloat}
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
    # have relative grid, find rational grid unit
    g⁻ = ratio_max(ratio(a⁻, c), ratio(s⁻, d), ratio(b⁻, e))
    g⁺ = ratio_min(ratio(a⁺, c), ratio(s⁺, d), ratio(b⁺, e))
    g = simplest_rational(g⁻, g⁺)
    # restore signs for endpoints
    signbit(a) && (c = -c)
    signbit(b) && (e = -e)
    # these should be true
    @assert a ≈ c*g[1]/g[2]
    @assert s ≈ d*g[1]/g[2]
    @assert b ≈ e*g[1]/g[2]
    # double precision grid unit:
    h, l = div_hi_lo(g...)
    FRange(c, d, n, h, l)
end
