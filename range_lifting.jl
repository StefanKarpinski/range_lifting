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

function simplest_between(x::T, y::T) where {T<:TwicePrecision}
    𝟘, 𝟙 = zero(T), one(T)
    if y < 𝟘
        n, d = simplest_between(-y, -x)
        return -n, d
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

    g = tz(D)
    z = N/D
    D′ = D
    while x ≤ (z′ = N/(D′ += 1))
        (g′ = tz(D′)) > g || continue
        g, z, D = g′, z′, D′
    end

    return N, D
end

@eval Base function one(::Type{TwicePrecision{T}}) where {T}
    TwicePrecision{T}(one(T), zero(T))
end

@eval Base function round(
    x::TwicePrecision{<:AbstractFloat},
    r::RoundingMode{mode} = RoundNearest,
) where {mode}
    if eps(x.hi) ≥ 1
        flip = mode in (:ToZero, :FromZero) && x.hi*x.lo < 0
        r_lo = flip ? -round(-x.lo) : round(x.lo)
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

mid(a::Float64, b::Float64) = TwicePrecision(0.5a) + TwicePrecision(0.5b)

function lift_range(a::Float64, s::Float64, b::Float64)
    # carefully compute (a+b)/2, (a-b)/2, n
    m = mid(a, -b)
    r = mid(a, +b)/m
    n = round(-m/0.5s)
    # TODO: bail if n is infinite
    # TODO: search for  n values are possible

    # initial bounds for a, s, b
    a⁻, a⁺ = mid(prevfloat(a), a), mid(a, nextfloat(a))
    s⁻, s⁺ = mid(prevfloat(s), s), mid(s, nextfloat(s))
    b⁻, b⁺ = mid(prevfloat(b), b), mid(b, nextfloat(b))

    # bounds for r = (a + b)/(a - b)
    r⁻ = r⁺ = r
    for a′ in (a⁻, a⁺), b′ in (b⁻, b⁺)
        r′ = (a′ + b′)/(a′ - b′)
        r⁻ = min(r⁻, r′)
        r⁺ = max(r⁺, r′)
    end

    # want simple f such that a - (q + f)*s == 0
    #   where q ∈ ℤ and |f| ≤ 1/2
    h = -0.5n
    q = round(h*(1 + r))
    f⁻ = h*(1 + r⁺) - q
    f⁺ = h*(1 + r⁻) - q
    # define x = a/s, y = b/s
    # f = F/d, x = X/d, y = Y/d
    F, d = simplest_between(f⁻, f⁺)
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
    S, D = simplest_between(s⁻, s⁺)

    # compute the zero point and step
    z = (F*S)/(D*d)
    ŝ = S/D

    [z + (k + q)*ŝ for k = 0:Int(n)]
end
