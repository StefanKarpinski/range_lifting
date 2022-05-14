# based on https://stackoverflow.com/a/65189151/659248

using Base: TwicePrecision

function ratio(x::TwicePrecision{<:AbstractFloat})
    d = inv(iszero(x.lo) ? eps(x.hi) : eps(x.lo))
    return x*d, TwicePrecision(d)
end

# powers of two an integer-valued TwicePrecision is divisible by (max 64)
function tz(x::TwicePrecision{F}) where {F<:Base.IEEEFloat}
    # n == x (mod Int)
    n = Signed(x.hi/eps(x.hi)) << exponent(eps(x.hi)) +
        Signed(x.lo/eps(x.lo)) << exponent(eps(x.lo))
    return trailing_zeros(n)
end

function simplest_rational(x::T, y::T) where {T<:TwicePrecision}
    𝟘, 𝟙 = zero(T), one(T)
    if y < 𝟘
        N, D = simplest_rational(-y, -x)
        return -N, D
    end
    x ≤ 𝟘 && return 𝟘, 𝟙

    s, t = ratio(x)
    u, v = ratio(y)

    a = d = 𝟙
    b = c = 𝟘

    while true
        q = (s - 𝟙) ÷ t
        s, t, u, v = v, u-q*v, t, s-q*t
        a, b, c, d = b+q*a, a, d+q*c, c
        s ≤ t && break
    end
    N, D = a + b, c + d

    # N has smallest possible absolute value
    # there can be multiple possible D values
    # we have the smallest one (always positive)
    # scan for potentially "simpler" denominators
    # our heuristic is having more factors of two

    D′ = D
    z = N/D′
    g = tz(D′)
    while x ≤ (z′ = N/(D′ += 1))
        (g′ = tz(D′)) > g || continue
        g, z, D = g′, z′, D′
    end

    return N, D
end

Base.zero(x::TwicePrecision) = zero(typeof(x))
Base.one(x::TwicePrecision) = one(typeof(x))
Base.one(T::Type{<:TwicePrecision}) = T(1, 0)

Base.copy(x::TwicePrecision) = x

@eval Base function round(
    x::TwicePrecision{<:AbstractFloat},
    r::RoundingMode{mode} = RoundNearest,
) where {mode}
    if eps(x.hi) ≥ 1
        flip = mode in (:ToZero, :FromZero) && x.hi*x.lo < 0
        r_lo = flip ? -round(-x.lo, r) : round(x.lo, r)
        return TwicePrecision(x.hi, r_lo)
    else
        next = nextfloat(x.hi, Int(sign(x.lo)))
        this = round(x.hi, r)
        that = round(next, r)
        this == that && return TwicePrecision(this)
        edge = mode in (:ToZero, :FromZero, :Up, :Down) ? 0.0 : 0.5
        frac = abs(x.hi - this)
        return TwicePrecision(frac == edge ? that : this)
    end
end

@eval Base function div(
    a::TwicePrecision{T},
    b::TwicePrecision{T},
    r::RoundingMode,
) where {T}
    round(a/b, r)
end

@eval Base inv(x::TwicePrecision) = one(typeof(x))/x
@eval Base abs(x::TwicePrecision) = signbit(x.hi) ? -x : x
@eval Base isless(x::TwicePrecision, y::TwicePrecision) = x < y
@eval Base bitstring(n::BigInt) = string(n, base=2)

int(x::TwicePrecision) = BigInt(x.hi) + BigInt(x.lo)

mid(a::Float64, b::Float64) = TwicePrecision(0.5a) + TwicePrecision(0.5b)

struct Interval{F<:AbstractFloat} <: Number
    lo::TwicePrecision{F}
    hi::TwicePrecision{F}
end
Interval(x::AbstractFloat) = Interval(mid(prevfloat(x), x), mid(x, nextfloat(x)))

# TODO: maybe unroll/optimize this
@inline lo_hi(op::Function, U::Interval, V::Interval) =
    extrema((op(U.lo, V.lo), op(U.lo, V.hi), op(U.hi, V.lo), op(U.hi, V.hi)))

Base.:+(U::Interval, V::Interval) = Interval(U.lo + V.lo, U.hi + V.hi)
Base.:-(U::Interval, V::Interval) = Interval(U.lo - V.hi, U.hi - V.lo)
Base.:*(U::Interval, V::Interval) = Interval(lo_hi(*, U, V)...)
Base.:/(U::Interval, V::Interval) = Interval(lo_hi(/, U, V)...)
Base.:∩(U::Interval, V::Interval) = Interval(max(U.lo, V.lo), min(U.hi, V.hi))

Base.:+(x::Real, V::Interval) = typeof(V)(x + V.lo, x + V.hi)
Base.:*(x::Real, V::Interval) = typeof(V)(minmax(x*V.lo, x*V.hi)...)
Base.:*(x::TwicePrecision, V::Interval) = Interval(minmax(x*V.lo, x*V.hi)...)

simplest_rational(V::Interval) = simplest_rational(V.lo, V.hi)

ilog10(x::TwicePrecision) = Int(floor(log10(x.hi))) # TODO: approximate

# pick integer in the interval with the most trailing zeros
function pick_int(V::Interval{F}) where {F<:AbstractFloat}
    𝟘 = zero(V.lo)
    V.hi < 𝟘 && return -pick_int(-V)
    V.lo ≤ 𝟘 && return 𝟘
    lo = round(V.lo, RoundUp)
    hi = round(V.hi, RoundDown)
    lo > hi && return oftype(lo, NaN)
    lo < hi || return lo
    @assert 𝟘 < lo < hi

    # find range of at most 10 good candidates
    l = ilog10(hi - lo)
    m = Int(floor(log(5, maxintfloat(F))))
    q, r = divrem(l, m)
    p = Base.power_by_squaring(TwicePrecision(F(10)^m), q)
    p *= F(10)^r
    n = round(lo/p, RoundUp)
    h = round(hi/p, RoundDown)

    # pick the one with the most factors of 2
    n′ = n
    g = tz(n′)
    while (n′ += 1) ≤ h
        (g′ = tz(n′)) > g || continue
        g, n = g′, n′
    end

    # remultiply by p
    n *= p
    @assert lo ≤ n ≤ hi
    return n
end

function lift_range(a::Float64, s::Float64, b::Float64)
    # bounds on real input values
    A = Interval(a)
    S = Interval(s)
    B = Interval(b)

    n = pick_int((B - A)/S)
    R = (A + B)/(A - B)
    Q = -0.5n*(1 + R)

    # want simple f such that a - (q + f)*s == 0
    #   where q ∈ ℤ and |f| ≤ 1/2
    h = -0.5n
    q = round(-0.5n*(1 + R))
    f⁻ = h*(1 + r⁺) - q
    f⁺ = h*(1 + r⁻) - q
    # define x = a/s, y = b/s
    # f = F/d, x = X/d, y = Y/d
    F, d = simplest_rational(f⁻, f⁺)
    X = F + q*d # x = f + q = (F + q*d)/d
    Y = X + n*d # y = x + n = (X + n*d)/d

    # tighten bounds on `s`
    # s = a/x = a/(X/d) = a*d/X
    s⁻′, s⁺′ = minmax(a⁻*d/X, a⁺*d/X)
    s⁻ = max(s⁻, s⁻′)
    s⁺ = min(s⁺, s⁺′)
    # s = b/y = b/(Y/d) = b*d/Y
    s⁻′, s⁺′ = minmax(b⁻*d/Y, b⁺*d/Y)
    s⁻ = max(s⁻, s⁻′)
    s⁺ = min(s⁺, s⁺′)

    # simplest rational for `s`
    S, D = simplest_rational(s⁻, s⁺)

    # compute the zero point and step
    z = (F*S)/(D*d)
    ŝ = S/D

    [z + (k + q)*ŝ for k = 0:Int(n)]
end
