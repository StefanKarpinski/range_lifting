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
    # @assert 0 < lo < hi
    e = exponent(hi - lo)
    b = floor(ldexp(hi, -e))
    a = max(lo, ldexp(b - 1, e))
    b = ldexp(b, e)
    m = tz(a) ≥ tz(b) ? a : b
    # @assert lo ≤ m ≤ hi
    return m
end

function simplest_rational(
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
    return n, d
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

# counter example: (a, s, b) = (-1e20, 3.0, 2e20)
# problem: can be made to hit zero but shouldn't!
# worse: (a, s, b) = (-1.0e17, 0.3, 2.0e18)
# another: (a, s, b) = (-1e14, .9, 8e15)

function lift_range(a::T, s::T, b::T) where {T<:AbstractFloat}
    a⁻, a⁺ = prevfloat(a), nextfloat(a)
    s⁻, s⁺ = prevfloat(s), nextfloat(s)
    b⁻, b⁺ = prevfloat(b), nextfloat(b)
    n⁻ = cld(b⁻ - a⁺, s⁺)
    n⁺ = fld(b⁺ - a⁻, s⁻)
    n = simplest_float(n⁻, n⁺)
    p_n = tz(n)
    # otherwise can't hit endpoint
    @assert p_n ≥ 0
    # find best grid divisor
    c = d = e = 0
    while true
        # next divisor
        d += 1
        # find simplest c
        c⁻ = cld(d*a⁻, s⁺)
        c⁺ = fld(d*a⁺, s⁻)
        c = simplest_float(c⁻, c⁺)
        p_c = tz(c)
        p_c ≥ p_n || continue
        # find simplest e
        e⁻ = cld(d*b⁻, s⁺)
        e⁺ = fld(d*b⁺, s⁻)
        e = simplest_float(e⁻, e⁺)
        p_e = tz(e)
        p_e ≥ p_n || continue
        # found good c & e
        break
    end
    return d, c, e
end
