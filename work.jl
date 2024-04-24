import Base: TwicePrecision, canonicalize2, div12

# not a generally correct definition, but good enough here
Base.isless(x::TwicePrecision, y::TwicePrecision) = x < y
Base.zero(x::TwicePrecision) = typeof(x)(zero(x.hi))
Base.one(x::TwicePrecision) = typeof(x)(one(x.hi))

Base.signbit(x::TwicePrecision) = iszero(x.hi) ? signbit(x.lo) : signbit(x.hi)
Base.isinteger(x::TwicePrecision) = isinteger(x.hi) & isinteger(x.lo)

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

Base.nextfloat(x::TwicePrecision, k::Integer=1) =
    TwicePrecision(canonicalize2(x.hi, nextfloat(x.lo, k))...)
Base.prevfloat(x::TwicePrecision, k::Integer=1) =
    TwicePrecision(canonicalize2(x.hi, prevfloat(x.lo, k))...)

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

    # TODO: eliminate common factors

    # check we're in the interval
    @assert lo ≤ n/d ≤ hi
    return n, d
end

function ival(x::T) where {T<:AbstractFloat}
    lo = (TwicePrecision(x) + TwicePrecision(prevfloat(x)))/2
    hi = (TwicePrecision(x) + TwicePrecision(nextfloat(x)))/2
    lo, hi
end

"""
    ratio_break⁺(x, y) -> r

Return a `TwicePrecision` value `r` such that:

    - `typeof(x, y*prevfloat(r)) == x`
    - `typeof(x, y*nextfloat(r)) != x`

Inputs can be floats or `TwicePrecision` floats.
"""
function ratio_break⁺(x::T, y::T) where {T<:AbstractFloat}
    x⁻ = x
    if signbit(y)
        x⁻, y = -x⁻, -y
    end
    x⁺ = nextfloat(x⁻)
    h = 0.5*(x⁻/y + x⁺/y)
    l = 0.5*(fma(-y, h, x⁻) + fma(-y, h, x⁺))/y
    while true
        if fma(y, h, y*l) ≤ x⁻
            while fma(y, h, y*l) ≤ x⁻
                l = nextfloat(l)
            end
            l = prevfloat(l)
        else
            while fma(y, h, y*l) ≥ x⁺
                l = prevfloat(l)
            end
            l = nextfloat(l)
        end
        h + l == h && break # canonical
        h, l = canonicalize2(h, l)
    end
    @assert (h, l) == canonicalize2(h, l)
    @assert fma(y, h, y*prevfloat(l)) == x⁻
    @assert fma(y, h, y*nextfloat(l)) == x⁺
    r = TwicePrecision(h, l)
end

function ratio_break⁺(
    x::TwicePrecision{T},
    y::TwicePrecision{T},
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
    @assert r*y == x
    @assert nextfloat(r)*y > x
    return r
end

"""
    ratio_break⁻(x, y) -> r

Return a `TwicePrecision` value `r` such that:

    - `typeof(x, y*prevfloat(r)) != x`
    - `typeof(x, y*nextfloat(r)) == x`

Inputs can be floats or `TwicePrecision` floats.
"""
function ratio_break⁻(x::T, y::T) where {T<:AbstractFloat}
    if signbit(y)
        x, y = -x, -y
    end
    ratio_break⁺(prevfloat(x), y)
end

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
    @assert r*y == x
    @assert prevfloat(r)*y < x
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
Base.step(r::FRange{T}) where {T<:AbstractFloat} = T(r.d*r.g)
Base.getindex(r::FRange{T}, i::Integer) where {T<:AbstractFloat} =
    T((TwicePrecision{T}(i-1)*r.d + r.c)*r.g)

function range_ratios(a::T, s::T, b::T) where {T<:AbstractFloat}
    # handle negative step
    if signbit(s)
        n, c, d, e = range_ratios(b, -s, a)
        return n, e, d, c
    end
    # double precision intervals for a, s, b
    a⁻, a⁺ = ival(a)
    s⁻, s⁺ = ival(s)
    b⁻, b⁺ = ival(b)
    # end-point/step ratio intervals
    r_a⁻ = ratio_break⁻(a⁻, signbit(a) ? s⁻ : s⁺)
    r_a⁺ = ratio_break⁺(a⁺, signbit(a) ? s⁺ : s⁻)
    r_b⁻ = ratio_break⁻(b⁻, signbit(b) ? s⁻ : s⁺)
    r_b⁺ = ratio_break⁺(b⁺, signbit(b) ? s⁺ : s⁻)
    # pick simplest range length
    n = T(simplest_float(r_b⁻ - r_a⁺, r_b⁺ - r_a⁻))
    # check if end-point can be hit
    p = tz(n)
    p ≥ 0 || error("end-point can't be hit (length)")
    # make a and b interval bounds positive
    if signbit(a)
        a⁻, a⁺ = -a⁺, -a⁻
        r_a⁻, r_a⁺ = -r_a⁺, -r_a⁻
    end
    if signbit(b)
        b⁻, b⁺ = -b⁺, -b⁻
        r_b⁻, r_b⁺ = -r_b⁺, -r_b⁻
    end
    # stabilize lower bounds
    r_ab⁻ = ratio_break⁻(a⁻, b⁺)
    r_ba⁻ = ratio_break⁻(b⁻, a⁺)
    while true
        changed = false
        # shrink based on length
        if r_a⁻ < r_b⁻ - n
            r_a⁻ = r_b⁻ - n
            changed = true
        end
        if r_b⁻ < r_a⁻ + n
            r_b⁻ = r_a⁻ + n
            changed = true
        end
        # shrink based on ratios
        if r_a⁻ < r_b⁻ * r_ab⁻
            r_a⁻ = r_b⁻ * r_ab⁻
            changed = true
        end
        if r_b⁻ < r_a⁻ * r_ba⁻
            r_b⁻ = r_a⁻ * r_ba⁻
            changed = true
        end
        changed || break
    end
    # stabilize upper bounds
    r_ab⁺ = ratio_break⁺(a⁺, b⁻)
    r_ba⁺ = ratio_break⁺(b⁺, a⁻)
    while true
        changed = false
        # shrink based on length
        if r_a⁺ > r_b⁺ - n
            r_a⁺ = r_b⁺ - n
            changed = true
        end
        if r_b⁺ > r_a⁺ + n
            r_b⁺ = r_a⁺ + n
            changed = true
        end
        # shrink based on ratios
        if r_a⁺ > r_b⁺ * r_ab⁺
            r_a⁺ = r_b⁺ * r_ab⁺
            changed = true
        end
        if r_b⁺ > r_a⁺ * r_ba⁺
            r_b⁺ = r_a⁺ * r_ba⁺
            changed = true
        end
        changed || break
    end
    # find common fraction interval
    q_a = round(prevfloat(r_a⁻), RoundDown)
    q_b = round(prevfloat(r_b⁻), RoundDown)
    f_a⁻, f_a⁺ = r_a⁻ - q_a, r_a⁺ - q_a
    f_b⁻, f_b⁺ = r_b⁻ - q_b, r_b⁺ - q_b
    f⁻, f⁺ = max(f_a⁻, f_b⁻), min(f_a⁺, f_b⁺)
    P = exp2(-p)
    f⁻ *= P; f⁺ *= P
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
