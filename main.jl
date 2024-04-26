import Base: TwicePrecision, canonicalize2, add12, div12

Base.isless(x::TwicePrecision, y::TwicePrecision) =
    isless(x.hi, y.hi) || isequal(x.hi, y.hi) && isless(x.lo, y.lo)
Base.:(<=)(x::TwicePrecision, y::TwicePrecision) =
    x.hi < y.hi || x.hi == y.hi && x.lo <= y.lo
Base.:(<)(x::TwicePrecision, y::TwicePrecision) =
    x.hi < y.hi || x.hi == y.hi && x.lo < y.lo

Base.zero(x::TwicePrecision) = typeof(x)(zero(x.hi))
Base.one(x::TwicePrecision) = typeof(x)(one(x.hi))

Base.signbit(x::TwicePrecision) = iszero(x.hi) ? signbit(x.lo) : signbit(x.hi)
Base.isinteger(x::TwicePrecision) = isinteger(x.hi) & isinteger(x.lo)

function Base.nextfloat(x::TwicePrecision)
    lo = nextfloat(x.lo)
    x.hi + lo == x.hi && return TwicePrecision(x.hi, lo)
    y = TwicePrecision(canonicalize2(x.hi, lo)...)
    lo = prevfloat(y.lo)
    y.hi + lo == y.hi && return TwicePrecision(y.hi, lo)
    return y
end

function Base.prevfloat(x::TwicePrecision)
    lo = prevfloat(x.lo)
    x.hi + lo == x.hi && return TwicePrecision(x.hi, lo)
    y = TwicePrecision(canonicalize2(x.hi, lo)...)
    lo = nextfloat(y.lo)
    y.hi + lo == y.hi && return TwicePrecision(y.hi, lo)
    return y
end

# more accurate twice precision addition
# based on "Bailey’s QD library": https://www.davidhbailey.com/dhbsoftware/
# via https://mycourses.aalto.fi/pluginfile.php/926578/mod_resource/content/1/9781489979810-c2.pdf (Algorithm 6)
function Base.:(+)(x::TwicePrecision{T}, y::TwicePrecision{T}) where T
    s_hi, s_lo = add12(x.hi, y.hi)
    t_hi, t_lo = add12(x.lo, y.lo)
    c = s_lo + t_hi
    v_hi, v_lo = canonicalize2(s_hi, c)
    w = t_lo + v_lo
    TwicePrecision(canonicalize2(v_hi, w)...)
end

# more accurate twice precision division
# based on "Bailey’s QD library": https://www.davidhbailey.com/dhbsoftware/
function Base.:(/)(x::TwicePrecision{T}, y::TwicePrecision{T}) where T
    q1 = x.hi/y.hi
    r = x - q1*y
    q2 = r.hi/y.hi
    r -= q2*y
    q3 = r.hi/y.hi
    TwicePrecision(canonicalize2(q1, q2)...) + TwicePrecision(q3)
end

normalize⁺(x::AbstractFloat) =
    !issubnormal(x) ? x : signbit(x) ? -zero(x) : floatmin(x)
normalize⁻(x::AbstractFloat) =
    !issubnormal(x) ? x : signbit(x) ? -floatmin(x) : zero(x)

function normalize⁺(x::TwicePrecision{T}) where {T<:AbstractFloat}
    issubnormal(x.hi) ? TwicePrecision(normalize⁺(x.hi)) :
    issubnormal(x.lo) ? TwicePrecision(canonicalize2(x.hi, normalize⁺(x.lo))) : x
end

function normalize⁻(x::TwicePrecision{T}) where {T<:AbstractFloat}
    issubnormal(x.hi) ? TwicePrecision(normalize⁻(x.hi)) :
    issubnormal(x.lo) ? TwicePrecision(canonicalize2(x.hi, normalize⁻(x.lo))) : x
end

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

tmul(x::T, y::TwicePrecision{T}) where {T<:AbstractFloat} =
    fma(x, y.hi, x*y.lo)

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
    lo.hi + simplest_float(TwicePrecision(lo.lo), hi - lo.hi)
end

# TODO: harden against overflow
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

    s, t = ratio(normalize⁺(lo))
    u, v = ratio(normalize⁻(hi))

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

    # eliminate common factors of two
    z = min(tz(n), tz(d))
    n *= exp2(-z)
    d *= exp2(-z)

    # check we're in the interval
    @assert lo ≤ n/d ≤ hi
    return n, d
end

function ival(x::T) where {T<:AbstractFloat}
    lo = (TwicePrecision(x) + TwicePrecision(prevfloat(x)))/2
    hi = (TwicePrecision(x) + TwicePrecision(nextfloat(x)))/2
    return lo, hi
end

"""
    ratio_break⁺(x, y) -> r

Return a `TwicePrecision` value `r` such that:

    - `oftype(x, y*r) == x`
    - `oftype(x, y*nextfloat(r)) != x`

Inputs can be floats or `TwicePrecision` floats.
"""
function ratio_break⁺(
    x :: TwicePrecision{T},
    y :: TwicePrecision{T},
) where {T<:AbstractFloat}
    if signbit(y)
        x, y = -x, -y
    end
    r = x/y
    while r*y ≤ x
        r = nextfloat(r)
    end
    while r*y > x
        r = prevfloat(r)
    end
    @assert y*r ≤ x
    @assert y*nextfloat(r) > x
    return r
end

function ratio_break⁺(x::T, y::T) where {T<:AbstractFloat}
    if signbit(y)
        x, y = -x, -y
    end
    # find largest double precision x⁺ such that T(x⁺) == x
    x⁺ = (TwicePrecision(x) + TwicePrecision(nextfloat(x)))/2
    T(x⁺) ≠ x && (x⁺ = prevfloat(x⁺))
    @assert T(x⁺) == x
    @assert T(nextfloat(x⁺)) == nextfloat(x)
    r = ratio_break⁺(x⁺, TwicePrecision(y))
    @assert T(y*r) == x
    @assert T(y*nextfloat(r)) != x
    return r
end

"""
    ratio_break⁻(x, y) -> r

Return a `TwicePrecision` value `r` such that:

    - `oftype(x, y*r) == x`
    - `oftype(x, y*prevfloat(r)) != x`

Inputs can be floats or `TwicePrecision` floats.
"""
function ratio_break⁻(
    x::TwicePrecision{T},
    y::TwicePrecision{T},
) where {T<:AbstractFloat}
    if signbit(y)
        x, y = -x, -y
    end
    r = x/y
    while r*y ≥ x
        r = prevfloat(r)
    end
    while r*y < x
        r = nextfloat(r)
    end
    @assert y*r ≥ x
    @assert y*prevfloat(r) < x
    return r
end

function ratio_break⁻(x::T, y::T) where {T<:AbstractFloat}
    if signbit(y)
        x, y = -x, -y
    end
    # find smallest double precision x⁻ such that T(x⁻) == x
    x⁻ = (TwicePrecision(x) + TwicePrecision(prevfloat(x)))/2
    T(x⁻) ≠ x && (x⁻ = nextfloat(x⁻))
    @assert T(x⁻) == x
    @assert T(prevfloat(x⁻)) == prevfloat(x)
    r = ratio_break⁻(x⁻, TwicePrecision(y))
    @assert T(y*r) == x
    @assert T(y*prevfloat(r)) != x
    return r
end

"""
    ratio_ival(x, y)

Shorthand for `ratio_break⁻(x, y), ratio_break⁺(x, y)`.
"""
function ratio_ival(x::T, y::T) where {T}
    ratio_break⁻(x, y), ratio_break⁺(x, y)
end

struct FRange{T<:AbstractFloat} <: AbstractRange{T}
    c::T
    d::T
    n::T
    g::TwicePrecision{T}
end

Base.length(r::FRange) = Int(r.n) + 1
Base.first(r::FRange) = r[1]
Base.step(r::FRange) = tmul(r.d, r.g)
Base.last(r::FRange) = eltype(r)((r.n*r.d + r.c)*r.g)

Base.getindex(r::FRange{T}, i::Integer) where {T<:AbstractFloat} =
    T((TwicePrecision{T}(i-1)*r.d + r.c)*r.g)

# Find simple integers for length n and integers (c, d, e) such that:
#
#   c/d ∈ [a]/[s]
#   e/d ∈ [b]/[s]
#   c/e ∈ [a]/[b]
#
function range_ratios(a::T, s::T, b::T) where {T<:AbstractFloat}
    # handle negative step
    if signbit(s)
        n, c, d, e = range_ratios(b, -s, a)
        return n, e, d, c
    end
    # double precision intervals for a, s, b
    a⁻, a⁺ = ival(abs(a))
    s⁻, s⁺ = ival(abs(s))
    b⁻, b⁺ = ival(abs(b))
    # end-point/step ratio intervals
    r_a⁻ = ratio_break⁻(a⁻, s⁺)
    r_a⁺ = ratio_break⁺(a⁺, s⁻)
    r_b⁻ = ratio_break⁻(b⁻, s⁺)
    r_b⁺ = ratio_break⁺(b⁺, s⁻)
    # signed ratio intervals
    sr_a⁻, sr_a⁺ = signbit(a) ? (-r_a⁺, -r_a⁻) : (r_a⁻, r_a⁺)
    sr_b⁻, sr_b⁺ = signbit(b) ? (-r_b⁺, -r_b⁻) : (r_b⁻, r_b⁺)
    # pick simplest range length
    n = T(simplest_float(sr_b⁻ - sr_a⁺, sr_b⁺ - sr_a⁻))
    # check if end-point can be hit
    p = tz(n)
    p ≥ 0 || error("end-point can't be hit (length)")
    # ratio intervals between end-points
    r_ab⁻ = ratio_break⁻(a⁻, b⁺)
    r_ab⁺ = ratio_break⁺(a⁺, b⁻)
    r_ba⁻ = ratio_break⁻(b⁻, a⁺)
    r_ba⁺ = ratio_break⁺(b⁺, a⁻)
    # stabilize ratio intervals
    while true
        changed = false
        # shrink [a] based on length
        if sr_a⁻ < sr_b⁻ - n
            sr_a⁻ = sr_b⁻ - n
            if !signbit(a)
                r_a⁻ = sr_a⁻
            else
                r_a⁺ = -sr_a⁻
            end
            changed = true
        end
        if sr_a⁺ > sr_b⁺ - n
            sr_a⁺ = sr_b⁺ - n
            if !signbit(a)
                r_a⁺ = sr_a⁺
            else
                r_a⁻ = -sr_a⁺
            end
            changed = true
        end
        # shrink [b] based on length
        if sr_b⁻ < sr_a⁻ + n
            sr_b⁻ = sr_a⁻ + n
            if !signbit(b)
                r_b⁻ = sr_b⁻
            else
                r_b⁺ = -sr_b⁻
            end
            changed = true
        end
        if sr_b⁺ > sr_a⁺ + n
            sr_b⁺ = sr_a⁺ + n
            if !signbit(b)
                r_b⁺ = sr_b⁺
            else
                r_b⁻ = -sr_b⁺
            end
            changed = true
        end
        # shrink [a] based on ratios
        if r_a⁻ < r_b⁻ * r_ab⁻
            r_a⁻ = r_b⁻ * r_ab⁻
            if !signbit(a)
                sr_a⁻ = r_a⁻
            else
                sr_a⁺ = -r_a⁻
            end
            changed = true
        end
        if r_a⁺ > r_b⁺ * r_ab⁺
            r_a⁺ = r_b⁺ * r_ab⁺
            if !signbit(a)
                sr_a⁺ = r_a⁺
            else
                sr_a⁻ = -r_a⁺
            end
            changed = true
        end
        # shrink [b] based on ratios
        if r_b⁻ < r_a⁻ * r_ba⁻
            r_b⁻ = r_a⁻ * r_ba⁻
            if !signbit(b)
                sr_b⁻ = r_b⁻
            else
                sr_b⁺ = -r_b⁻
            end
            changed = true
        end
        if r_b⁺ > r_a⁺ * r_ba⁺
            r_b⁺ = r_a⁺ * r_ba⁺
            if !signbit(b)
                sr_b⁺ = r_b⁺
            else
                sr_b⁻ = -r_b⁺
            end
            changed = true
        end
        changed || break
    end
    # find common fraction interval
    f⁻, f⁺ = abs(a) ≤ abs(b) ? (sr_a⁻, sr_a⁺) : (sr_b⁻, sr_b⁺)
    f⁻ *= exp2(-p); f⁺ *= exp2(-p)
    q = round(prevfloat(f⁻), RoundDown)
    f⁻ -= q; f⁺ -= q
    f⁻ ≤ f⁺ || error("end-point can't be hit (ratios)")
    # find simplest rational in interval
    d = T(simplest_rational_core(f⁻, f⁺)[2])
    # find simplest end-point ratios
    c = T(simplest_float(d*r_a⁻, d*r_a⁺))
    e = T(simplest_float(d*r_b⁻, d*r_b⁺))
    # eliminate common powers of two
    z = min(tz(c), tz(d), tz(e))
    @assert z ≥ -p
    t = exp2(-z)
    c *= t; d *= t; e *= t
    # check that c:e matches a:b
    @assert a⁻*e ≤ b⁺*c
    @assert a⁺*e ≥ b⁻*c
    # check that c:d matches a:s
    @assert a⁻*d ≤ s⁺*c
    @assert a⁺*d ≥ s⁻*c
    # check that e:d matches b:s
    @assert b⁻*d ≤ s⁺*e
    @assert b⁺*d ≥ s⁻*e
    # restore end-point signs
    signbit(a) && (c = -c)
    signbit(b) && (e = -e)
    # check length
    @assert d*n == e - c
    # return values
    return n, c, d, e
end

function lift_range(a::T, s::T, b::T) where {T<:AbstractFloat}
    # find the relative grid ratios
    n, c, d, e = range_ratios(a, s, b)
    # still need rational value g:
    #  - g = s/d = a/c = b/e
    # get double precision bounds on g:
    lo_a, hi_a = ratio_ival(a, c)
    lo_s, hi_s = ratio_ival(s, d)
    lo_b, hi_b = ratio_ival(b, e)
    lo = max(lo_a, lo_s, lo_b)
    hi = min(hi_a, hi_s, hi_b)
    @assert lo ≤ hi # otherwise can't work
    num, den = simplest_rational(lo, hi)
    g = num/den
    @assert lo ≤ g ≤ hi
    # check that inputs are hit
    @assert tmul(c, g) == a
    @assert tmul(d, g) == s
    @assert tmul(e, g) == b
    # return range object
    FRange(c, d, n, g)
end
