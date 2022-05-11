# based on https://stackoverflow.com/a/65189151/659248

using Base: TwicePrecision

function ratio(x::TwicePrecision{<:AbstractFloat})
    d = inv(iszero(x.lo) ? eps(x.hi) : eps(x.lo))
    return x*d, TwicePrecision(d)
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
        s ≤ t && return a + b, c + d
    end
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
@eval Base isless(x::TwicePrecision, y::TwicePrecision) = x < y

mid(a::Float64, b::Float64) = TwicePrecision(0.5a) + TwicePrecision(0.5b)

function lift_range(a::Float64, s::Float64, b::Float64)
    # carefully compute (a+b)/2, (a-b)/2, n, n/2
    m = mid(a, -b)
    r = mid(a, +b)/m
    n = round(-m/0.5s) # TODO: bail if n is infinite

    # bounds for `a`, `b` and `r = (a + b)/(a - b)`
    a⁻, a⁺ = mid(prevfloat(a), a), mid(a, nextfloat(a))
    b⁻, b⁺ = mid(prevfloat(b), b), mid(b, nextfloat(b))
    r⁻ = r⁺ = r
    for a′ in (a⁻, a⁺), b′ in (b⁻, b⁺)
        r′ = (a′ + b′)/(a′ - b′)
        r⁻ = min(r⁻, r′)
        r⁺ = max(r⁺, r′)
    end

    # want simple `F` such that `a + (q + F)*s == 0`
    # where `q ∈ ℤ` and `-1/2 ≤ F ≤ 1/2`
    n½ = 0.5n
    q = round(n½*(1 + r))
    F⁻ = n½*(1 + r⁻) - q
    F⁺ = n½*(1 + r⁺) - q
    # F = f/d, X = x/d, Y = y/d
    f, d = simplest_between(F⁻, F⁺)
    x = f + q*d # X = F + q = (f + q*d)/d
    y = x - n*d # Y = X - n = (x - n*d)/d

    # use `x/y` for better bounds on `a`
    a⁻′, a⁺′ = minmax(b⁻*x/y, b⁺*x/y)
    a⁻ = max(a⁻, a⁻′)
    a⁺ = min(a⁺, a⁺′)

    # simplest rational for `a`
    A, D = simplest_between(a⁻, a⁺)
    Dx = D*x

    # and finally get our lifted values
    â = A/D
    b̂ = (A*y)/Dx
    ŝ = A*(y - x)/(Dx*n)

    return â, ŝ, b̂
end
