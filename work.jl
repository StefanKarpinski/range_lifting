import Base: TwicePrecision, canonicalize2, div12

# not a generally correct definition, but good enough here
Base.isless(x::TwicePrecision, y::TwicePrecision) = x < y
Base.zero(x::TwicePrecision) = typeof(x)(zero(x.hi))
Base.one(x::TwicePrecision) = typeof(x)(one(x.hi))

function Base.round(
    x::TwicePrecision{<:AbstractFloat},
    R::RoundingMode{mode} = RoundNearest,
) where {mode}
    if eps(x.hi) ≥ 1
        flip = mode in (:ToZero, :FromZero) && x.hi*x.lo < 0
        r_lo = flip ? -round(-x.lo, R) : round(x.lo, R)
        return TwicePrecision(x.hi, r_lo)
    else
        next = nextfloat(x.hi, Int(sign(x.lo)))
        this = round(x.hi, R)
        that = round(next, R)
        this == that && return TwicePrecision(this)
        edge = mode in (:ToZero, :FromZero, :Up, :Down) ? 0.0 : 0.5
        frac = abs(x.hi - this)
        return TwicePrecision(frac == edge ? that : this)
    end
end

function Base.div(
    a::TwicePrecision{T},
    b::TwicePrecision{T},
    R::RoundingMode,
) where {T}
    round(a/b, R)
end

Base.nextfloat(x::TwicePrecision) =
    TwicePrecision(canonicalize2(x.hi, nextfloat(x.lo))...)
Base.prevfloat(x::TwicePrecision) =
    TWicePrecision(canonicalize2(x.hi, prevfloat(x.lo))...)

function tz(x::T) where {T<:AbstractFloat}
    iszero(x) && return typemax(Int)
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

function simplest_float(
    lo :: TwicePrecision{T},
    hi :: TwicePrecision{T},
) where {T<:AbstractFloat}
    lo.hi == hi.hi &&
        return TwicePrecision(lo.hi, simplest_float(lo.lo, hi.lo))
    @assert lo.hi < hi.hi
    l = lo.lo ≤ 0 ? lo.hi : nextfloat(lo.hi)
    h = hi.lo ≥ 0 ? hi.hi : prevfloat(hi.hi)
    l ≤ h && return TwicePrecision(simplest_float(l, h))
    @assert 0 < lo.lo && hi.lo < 0
    h = hi - lo.hi
    @assert iszero(h.lo)
    m = simplest_float(lo.lo, h.hi)
    return TwicePrecision(canonicalize2(lo.hi, m)...)
end

function ratio(x::TwicePrecision{T}) where {T<:AbstractFloat}
    p = min(0, tz(x))
    n = TwicePrecision(ldexp(x.hi, -p), ldexp(x.lo, -p))
    d = TwicePrecision(exp2(-p))
    return n, d
end

# based on https://stackoverflow.com/a/65189151/659248
function simplest_rational_core(
    lo :: TwicePrecision{T},
    hi :: TwicePrecision{T},
) where {T<:AbstractFloat}
    𝟘 = zero(lo)
    𝟙 = one(lo)

    @assert 𝟘 < lo < hi

    s, t = ratio(lo)
    u, v = ratio(hi)

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
    lo :: TwicePrecision{T},
    hi :: TwicePrecision{T},
) where {T<:AbstractFloat}
    𝟘 = zero(lo)
    𝟙 = one(lo)

    # reduce to positive case
    if hi < 𝟘
        n, d = simplest_rational(-hi, -lo)
        return -n, d
    end
    lo ≤ 𝟘 && return 0, 𝟙

    # if there are integers, return the simplest one
    if round(lo, RoundUp) ≤ round(hi, RoundDown)
        return simplest_float(lo, hi), 𝟙
    end

    # find strictly minimal solution
    n, d = simplest_rational_core(lo, hi)

    return n, d

    # find numerator bounds: d*lo < n < d*hi
    n⁻ = round(d*lo, RoundUp)
    while n⁻ < n && n⁻/d ≤ lo
        n⁻ = nextfloat(n⁻)
    end
    n⁺ = round(d*hi, RoundDown)
    while n⁺ > n && hi ≤ n⁺/d
        n⁻ = prevfloat(n⁻)
    end

    # pick simplest numerator
    n = simplest_float(n⁻, n⁺)

    return n, d
end

function g_ival(a::T, c::T) where {T<:AbstractFloat}
    a, c = abs(a), abs(c)
    h = a/c
    # lower bound (strict)
    a⁻ = prevfloat(a)
    h⁻ = h + 0.5*(fma(-c, h, a) + fma(-c, h, a⁻))/c
    l⁻ = nextfloat(0.5*(fma(-c, h⁻, a) + fma(-c, h⁻, a⁻))/c)
    @assert (h⁻, l⁻) == canonicalize2(h⁻, l⁻)
    @assert fma(c, h⁻, c*l⁻) > a⁻
    while fma(c, h⁻, c*l⁻) > a⁻
        l⁻ = prevfloat(l⁻)
    end
    h⁻, l⁻ == canonicalize2(h⁻, l⁻)
    @assert fma(c, h⁻, c*nextfloat(l⁻)) == a
    @assert fma(c, h⁻, c*l⁻) == a⁻
    g⁻ = TwicePrecision(h⁻, l⁻)
    # upper bound (strict)
    a⁺ = nextfloat(a)
    h⁺ = h + 0.5*(fma(-c, h, a) + fma(-c, h, a⁺))/c
    l⁺ = prevfloat(0.5*(fma(-c, h⁺, a) + fma(-c, h⁺, a⁺))/c)
    @assert (h⁺, l⁺) == canonicalize2(h⁺, l⁺)
    @assert fma(c, h⁺, c*l⁺) < a⁺
    while fma(c, h⁺, c*l⁺) < a⁺
        l⁺ = nextfloat(l⁺)
    end
    h⁺, l⁺ == canonicalize2(h⁺, l⁺)
    @assert fma(c, h⁺, c*prevfloat(l⁺)) == a
    @assert fma(c, h⁺, c*l⁺) == a⁺
    g⁺ = TwicePrecision(h⁺, l⁺)
    # return interval (exclusive)
    g⁻, g⁺
end

struct FRange{T<:AbstractFloat} <: AbstractRange{T}
    c::T
    d::T
    n::T
    g::TwicePrecision{T}
end

Base.length(r::FRange) = Int(r.n) + 1
Base.step(r::FRange{T}) where {T<:AbstractFloat} = T(r.d*r.g)
Base.getindex(r::FRange{T}, i::Integer) where {T<:AbstractFloat} =
    T((TwicePrecision{T}(i-1)*r.d + r.c)*r.g)

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
    lo_a, hi_a = g_ival(a, c)
    lo_b, hi_b = g_ival(b, e)
    lo = max(lo_a, lo_b)
    hi = min(hi_a, hi_b)
    num, den = simplest_rational(lo, hi)
    g = num/den
    @assert lo < g < hi
    # check: end-points hit exactly, step approximately
    @assert T(c*g) == a
    @assert T(d*g) ≈  s
    @assert T(e*g) == b
    # return range object
    FRange(c, d, n, g)
end

# example: (a, s, b) = (0.2, 0.1, 1.1)
# example: (a, s, b) = (-3e50, 1e50, 4e50)
# problem: can be made to hit zero but shouldn't!
# example: (a, s, b) = (-1e20, 3.0, 2e20)
# worse: (a, s, b) = (-1.0e17, 0.3, 2.0e18)
# another: (a, s, b) = (-1e14, .9, 8e15)
