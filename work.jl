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

# based on https://stackoverflow.com/a/65189151/659248 (inclusive version)
function simplest_rational_core(
    lo :: TwicePrecision{T},
    hi :: TwicePrecision{T},
) where {T<:AbstractFloat}
    𝟘 = zero(lo)
    𝟙 = one(lo)

    @assert 𝟘 < lo ≤ hi

    s, t = ratio(lo)
    u, v = ratio(hi)

    a = d = 𝟙
    b = c = 𝟘

    while true
        q = (s - 𝟙) ÷ t
        s, t, u, v = v, u-q*v, t, s-q*t
        a, b, c, d = b+q*a, a, d+q*c, c
        s ≤ t && break
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

    # simplify numerator and denominator
    n = simplest_float(d*lo, d*hi)
    d = simplest_float(n/hi, n/lo)

    # check we're in the interval
    @assert lo ≤ n/d ≤ hi
    return n, d
end

"""
    ratio_ival((x⁻, x⁺), y)
    ratio_ival(x, y)

Returns a pair of `TwicePrecision` values, `(r⁻, r⁺)`, which bound the region
the ratio `x/y` could be, in the sense that they are the tightest values such
that `y*r⁻ == x⁻` and `y*r⁺ == x⁺`. When only a single `x` value is given
then `x⁻ = prevfloat(x)` and `x⁺ = nextfloat(x)` are used.
"""
function ratio_ival((x⁻, x⁺)::Tuple{T,T}, y::T) where {T<:AbstractFloat}
    if signbit(y)
        x⁻, x⁺ = -x⁺, -x⁻
        y = -y
    end
    @assert nextfloat(x⁻) ≤ prevfloat(x⁺)
    # lower bound (strict)
    x = nextfloat(x⁻)
    h⁻ = x⁻/y
    h⁻ = h⁻ + 0.5*(fma(-y, h⁻, x) + fma(-y, h⁻, x⁻))/y
    l⁻ = 0.5*(fma(-y, h⁻, x) + fma(-y, h⁻, x⁻))/y
    while fma(y, h⁻, y*l⁻) > x⁻
        l⁻ = prevfloat(l⁻)
    end
    while fma(y, h⁻, y*l⁻) ≤ x⁻
        l⁻ = nextfloat(l⁻)
    end
    @assert fma(y, h⁻, y*l⁻) == x
    @assert fma(y, h⁻, y*prevfloat(l⁻)) == x⁻
    @assert (h⁻, l⁻) == canonicalize2(h⁻, l⁻)
    r⁻ = TwicePrecision(h⁻, l⁻)
    # upper bound (strict)
    x = prevfloat(x⁺)
    h⁺ = x⁺/y
    h⁺ = h⁺ + 0.5*(fma(-y, h⁺, x) + fma(-y, h⁺, x⁺))/y
    l⁺ = 0.5*(fma(-y, h⁺, x) + fma(-y, h⁺, x⁺))/y
    while fma(y, h⁺, y*l⁺) < x⁺
        l⁺ = nextfloat(l⁺)
    end
    while fma(y, h⁺, y*l⁺) ≥ x⁺
        l⁺ = prevfloat(l⁺)
    end
    @assert fma(y, h⁺, y*l⁺) == x
    @assert fma(y, h⁺, y*nextfloat(l⁺)) == x⁺
    @assert (h⁺, l⁺) == canonicalize2(h⁺, l⁺)
    r⁺ = TwicePrecision(h⁺, l⁺)
    # return interval (exclusive)
    @assert r⁻ < r⁺
    r⁻, r⁺
end

ratio_ival(x::T, y::T) where {T<:AbstractFloat} =
    ratio_ival((prevfloat(x), nextfloat(x)), y)

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
    lo_a, hi_a = ratio_ival(a, c)
    lo_s, hi_s = ratio_ival(s, d)
    lo_b, hi_b = ratio_ival(b, e)
    lo = max(lo_a, lo_s, lo_b)
    hi = min(hi_a, hi_s, hi_b)
    @assert lo < hi # otherwise can't work
    num, den = simplest_rational(lo, hi)
    g = num/den
    @assert lo ≤ g ≤ hi
    # check that inputs are hit
    @assert T(c*g) == a
    @assert T(d*g) == s
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

# example: (a, s, b) = (1/10 + pi, 2/10, 19/10 + pi)
# - this works but makes range_ratios really slow
# - need faster approach than linear scanning
# example: (a, s, b) = (1/10 + x, 2/10, 19/10 + x)
# - with x = 0.6367464963941911
# - lo < hi fails, may need higher precision range_ratios
