# based on https://stackoverflow.com/a/65189151/659248

function simplest_between(s::R, t::R, u::R, v::R) where {R}
    𝟘, 𝟙 = zero(R), one(R)

    if widemul(u, t) < widemul(s, v)
        s, u = u, s
        t, v = v, t
    end
    if (u < 𝟘) ⊻ (v < 𝟘) # u/v < 0
        n, d = simplest_between(-u, v, -s, t)
        return -n, d
    end
    if (s > 𝟘) ⊻ (t > 𝟘) # s/t ≤ 0
        return 𝟘, 𝟙
    end

    a = d = 𝟙
    b = c = 𝟘

    while true
        q = (s - 𝟙) ÷ t
        s, t, u, v = v, u-q*v, t, s-q*t
        a, b, c, d = b+q*a, a, d+q*c, c
        s ≤ t && return a+b, c+d
    end
end

function simplest_between(x::Rational, y::Rational)
    Rational(simplest_between(
        numerator(x), denominator(x),
        numerator(y), denominator(y),
    )...)
end

@eval Base function one(::Type{TwicePrecision{T}}) where {T}
    TwicePrecision{T}(one(T), zero(T))
end

@eval Base function round(x::TwicePrecision, r::RoundingMode{mode}) where {mode}
    if eps(x.hi) ≥ 1
        return TwicePrecision(x.hi, round(x.lo, r))
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

widemul(x, y) = Base.widemul(x, y)
widemul(x::Base.TwicePrecision, y::Base.TwicePrecision) = x*y

function twice_precision(k::Integer)
    hi = float(k)
    lo = float(k - oftype(k, hi))
    Base.TwicePrecision(hi, lo)
end

int(x::Integer) = x
int(x::Base.TwicePrecision) = Int(x.hi) + Int(x.lo)

function lift_range(a::Float64, s::Float64, b::Float64)
    n = round(Int, (b - a)/s)
    q = round(Int, (1 + (a + b)/(a - b))*(n/2))
    A, pᴬ, σᴬ = Base.decompose(a); A *= σᴬ
    B, pᴮ, σᴮ = Base.decompose(b); B *= σᴮ
    p = min(pᴬ, pᴮ)
    A <<= 1 + pᴬ - p
    B <<= 1 + pᴮ - p
    eᴬ = 1 << (pᴬ - p)
    eᴮ = 1 << (pᴮ - p)
    # TODO: check that 0 ∉ (A - B) ± (eᴬ + eᴮ)
    # (otherwise interior extrema can occur)
    # (can only happen with unequal subnormals)
    R⁻ = R⁺ = (A + B)//(A - B)
    for dᴬ in (-eᴬ, eᴬ), dᴮ in (-eᴮ, eᴮ)
        R = ((A + dᴬ) + (B + dᴮ))//((A + dᴬ) - (B + dᴮ))
        R < R⁻ && (R⁻ = R)
        R > R⁺ && (R⁺ = R)
    end
    r⁻ = n*(1 + R⁻)/2 - q
    r⁺ = n*(1 + R⁺)/2 - q
    r = simplest_between(r⁻, r⁺)
    x = r + q
    y = x/(x-n)
    A⁻ = max((A - eᴬ)//1, (B - eᴮ)*y)
    A⁺ = min((A + eᴬ)//1, (B + eᴮ)*y)
    N⁻ = twice_precision(numerator(A⁻))
    N⁺ = twice_precision(numerator(A⁺))
    D⁻ = twice_precision(denominator(A⁻))*exp2(-p+1)
    D⁺ = twice_precision(denominator(A⁺))*exp2(-p+1)
    N, D = simplest_between(N⁻, D⁻, N⁺, D⁺)
    â = Int(N)//Int(D)
    b̂ = â/y
    ŝ = (b̂-â)/n
    return â, ŝ, b̂
end
